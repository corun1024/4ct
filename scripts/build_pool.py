#!/usr/bin/env python3
"""Build the `FourColor` modules under a job-count and a memory budget.

Lake starts as many jobs as the machine has hardware threads and offers no way
to say fewer, which makes a build on many cores memory-bandwidth-bound and a
build pinned to a few cores thrash.  This runs the same `lean` invocations Lake
would, in dependency order, but never more than `--jobs` at a time and never
admitting a module whose predicted peak would push the total past `--memory`.
It writes the same `.olean`/`.ilean` files into `.lake/build`, which is all
`lake env lean` needs to import the development.  Lake's own trace files are
*not* written, so `lake build` would not adopt this output — it would rebuild
everything, at one job per hardware thread.  Build the package with this
script, not with `lake build`.

Scheduling is driven by a cost table of per-module wall time and peak memory
(`scripts/module_cost.tsv`, committed; measurements from this machine overlay
it from `.lake/build/module_cost.tsv`).  Ready modules are ordered by critical
path — a module's own time plus the longest chain of modules waiting on it —
so that the long poles start early, and a module that does not fit the
remaining memory budget is skipped over in favour of one that does.

The table is a *hint*.  The dependency graph is always parsed afresh from the
sources, so a missing, stale or plain wrong table costs packing quality and
nothing else; the build is the same build.

It is incremental: a module whose `.olean` is newer than its source and than
every dependency's `.olean` is skipped.  `--clean` rebuilds everything.

Usage, from the project root, after `lake exe cache get`:

    scripts/build_pool.py [--jobs N] [--memory GB] [--clean] [--dry-run]
"""
import argparse
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

LEAN_OPTS = ['-Dpp.unicode.fun=true', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
             '-Dweak.linter.mathlibStandardSet=true', '-DmaxSynthPendingDepth=3']

PROFILE = 'scripts/module_cost.tsv'
LOCAL_PROFILE = '.lake/build/module_cost.tsv'
# p90 of the measured distribution: above the typical module, below the tail,
# so an unprofiled module errs towards admitting fewer jobs beside it.
ASSUME_MB = 4096
ASSUME_SECONDS = 30.0
JOBS_CAP = 32          # past this the build is memory-bandwidth-bound, not CPU-bound
DRIFT = 1.25           # report a module that exceeded its prediction by this much


def modules():
    mods = {}
    for dirpath, _, files in os.walk('FourColor'):
        for f in files:
            if f.endswith('.lean'):
                path = os.path.join(dirpath, f)
                name = 'FourColor.' + path[len('FourColor/'):-5].replace('/', '.')
                mods[name] = path
    mods['FourColor'] = 'FourColor.lean'
    return mods


def imports(path):
    with open(path) as fh:
        text = fh.read(200000)
    return set(re.findall(r'^import (FourColor(?:\.[A-Za-z0-9_]+)*)\s*$', text, re.M))


def uptodate(name, path, deps):
    """Whether `name`'s olean is newer than its source and than every dependency's.

    Lake's own trace files are not consulted, so this is deliberately
    conservative: any doubt rebuilds, and the `lake build` that follows would
    catch a wrong skip anyway.
    """
    olean = os.path.join('.lake/build/lib/lean', name.replace('.', '/') + '.olean')
    if not os.path.exists(olean):
        return False
    t = os.path.getmtime(olean)
    if t <= os.path.getmtime(path):
        return False
    for d in deps:
        dol = os.path.join('.lake/build/lib/lean', d.replace('.', '/') + '.olean')
        if not os.path.exists(dol) or t <= os.path.getmtime(dol):
            return False
    return True


def load_profile(paths, warn):
    """`{module: (seconds, peak_mb)}`, later files overriding earlier ones.

    A table that cannot be read at all is a warning, not an error: the build
    proceeds on the defaults.
    """
    prof = {}
    for p in paths:
        if not os.path.exists(p):
            continue
        try:
            bad = 0
            with open(p) as fh:
                for line in fh:
                    line = line.strip()
                    if not line or line.startswith('#'):
                        continue
                    f = line.split()
                    try:
                        prof[f[0]] = (float(f[1]), int(f[2]))
                    except (IndexError, ValueError):
                        bad += 1
            if bad:
                warn.append(f'{p}: {bad} unreadable rows ignored')
        except OSError as e:
            warn.append(f'{p}: {e}; scheduling on defaults')
    return prof


def save_profile(path, prof, measured):
    """Write the table, this run's measurements overriding what was loaded."""
    merged = dict(prof)
    merged.update(measured)
    try:
        d = os.path.dirname(path)
        if d:
            os.makedirs(d, exist_ok=True)
        with open(path, 'w') as fh:
            fh.write('# module\tseconds\tpeak_mb -- written by scripts/build_pool.py\n')
            for m in sorted(merged):
                s, mb = merged[m]
                fh.write(f'{m}\t{s:.1f}\t{mb}\n')
    except OSError as e:
        print(f'warning: could not write {path}: {e}', file=sys.stderr)


def critical_path(mods, deps, seconds):
    """`{module: own time + the longest chain of modules waiting on it}`.

    Ordering by this beats both raw duration (which starts a long leaf ahead of
    a short module that unblocks half the build) and dependency fan-out (which
    ignores how long anything takes).
    """
    dependents = {m: [] for m in mods}
    for m in mods:
        for d in deps[m]:
            if d in dependents:
                dependents[d].append(m)
    cp = {}
    for start in mods:
        if start in cp:
            continue
        stack = [(start, False)]
        while stack:
            m, expanded = stack.pop()
            if expanded:
                if m not in cp:
                    cp[m] = seconds(m) + max((cp[x] for x in dependents[m]), default=0.0)
            elif m not in cp:
                stack.append((m, True))
                for x in dependents[m]:
                    if x not in cp:
                        stack.append((x, False))
    return cp


def admit(ready, running_n, running_mb, jobs, budget_mb, mb):
    """The modules to start now, highest critical path first.

    A module that does not fit the remaining budget is skipped over rather than
    waited for, so one heavy module cannot idle the machine behind it.  With
    nothing running at all, the head of the queue starts regardless of its
    prediction — otherwise a module predicted above the whole budget could
    never run.
    """
    start, i = [], 0
    while i < len(ready) and running_n + len(start) < jobs:
        m = ready[i]
        need = mb(m)
        if (running_n or start) and running_mb + need > budget_mb:
            i += 1
            continue
        start.append(ready.pop(i))
        running_mb += need
    return start


def simulate(mods, deps, done, cp, seconds, mb, jobs, budget_mb):
    """Predicted makespan, by running the scheduler against the cost table."""
    pending, running, now, finished = set(mods) - done, [], 0.0, set(done)
    while pending or running:
        ready = sorted((m for m in pending if deps[m] <= finished), key=lambda m: -cp[m])
        used = sum(mb(m) for _, m in running)
        for m in admit(ready, len(running), used, jobs, budget_mb, mb):
            pending.discard(m)
            running.append((now + seconds(m), m))
        if not running:
            break
        running.sort()
        now, m = running.pop(0)
        finished.add(m)
    return now


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--jobs', type=int, help=f'max concurrent lean processes [min({JOBS_CAP}, 90%% of cores)]')
    ap.add_argument('--memory', type=float, help='budget in GB for the sum of predicted peaks [75%% of available]')
    ap.add_argument('--profile', default=PROFILE, help=f'committed cost table [{PROFILE}]')
    ap.add_argument('--save-profile', default=LOCAL_PROFILE, help=f'where to write the updated table [{LOCAL_PROFILE}]')
    ap.add_argument('--assume-mb', type=int, default=ASSUME_MB, help=f'peak assumed for an unprofiled module [{ASSUME_MB}]')
    ap.add_argument('--clean', action='store_true', help='rebuild every FourColor module')
    ap.add_argument('--dry-run', action='store_true', help='print the plan and stop')
    ap.add_argument('--log', default='build_pool.log')
    args = ap.parse_args()

    if args.jobs is None:
        args.jobs = max(1, min(JOBS_CAP, int((os.cpu_count() or 4) * 0.9)))
    if args.memory is None:
        avail = None
        try:
            with open('/proc/meminfo') as fh:
                for line in fh:
                    if line.startswith('MemAvailable:'):
                        avail = int(line.split()[1]) / 1024 / 1024
        except OSError:
            pass
        args.memory = (avail or 8.0) * 0.75
    budget_mb = args.memory * 1024

    warn = []
    allmods = modules()
    alldeps = {m: {d for d in imports(p) if d in allmods} for m, p in allmods.items()}
    # only what the root module reaches: stray files in the tree are not part of the proof
    reach, stack = set(), ['FourColor']
    while stack:
        m = stack.pop()
        if m in reach:
            continue
        reach.add(m); stack += list(alldeps[m])
    mods = {m: allmods[m] for m in reach}
    deps = {m: alldeps[m] for m in reach}

    prof = load_profile([args.profile, args.save_profile], warn)
    missing = [m for m in mods if m not in prof]
    stale = [m for m in prof if m not in mods]
    known = [s for m, (s, _) in prof.items() if m in mods]
    default_s = sorted(known)[len(known) // 2] if known else ASSUME_SECONDS

    def seconds(m):
        return prof[m][0] if m in prof else default_s

    def mb(m):
        return prof[m][1] if m in prof else args.assume_mb

    if missing:
        warn.append(f'{len(missing)} of {len(mods)} modules are not in the cost table, '
                    f'assuming {args.assume_mb} MB and {default_s:.0f}s each')
        if len(missing) > len(mods) // 2:
            warn.append('most of the build is unprofiled: this run will pack poorly, '
                        'the next one will not')
    if stale:
        warn.append(f'{len(stale)} cost-table entries no longer name a module (dropped on rewrite)')
    for w in warn:
        print(f'warning: {w}', file=sys.stderr)

    cp = critical_path(mods, deps, seconds)

    # `--clean --dry-run` plans a full build without destroying the current one.
    if args.clean and not args.dry_run:
        subprocess.run(['rm', '-rf', '.lake/build/lib/lean/FourColor', '.lake/build/lib/lean/FourColor.olean',
                        '.lake/build/lib/lean/FourColor.ilean'])
    done, running, failed = set(), {}, []
    pending = set(mods)
    if not args.clean:
        # Repeat to a fixed point, so that a module whose dependency must be
        # rebuilt is itself rebuilt.
        progress = True
        while progress:
            progress = False
            for m in list(pending):
                if deps[m] <= done and uptodate(m, mods[m], deps[m]):
                    pending.discard(m); done.add(m); progress = True
        if done:
            print(f'up to date: {len(done)} modules; {len(pending)} to build', flush=True)

    work = sum(seconds(m) for m in pending)
    eta = simulate(mods, deps, done, cp, seconds, mb, args.jobs, budget_mb)
    print(f'plan: {len(pending)} modules, {work / 3600:.1f} core-hours, '
          f'{args.jobs} jobs, {args.memory:.0f} GB budget, predicted {eta / 60:.0f} min', flush=True)
    if args.dry_run:
        return 0

    env = dict(os.environ)
    env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True,
                                      text=True, check=True).stdout.strip()
    root = os.getcwd()

    def run(name, path):
        out = os.path.join('.lake/build/lib/lean', name.replace('.', '/'))
        os.makedirs(os.path.dirname(out), exist_ok=True)
        cmd = ['lean', '-R', root] + LEAN_OPTS + ['-o', out + '.olean', '-i', out + '.ilean', path]
        t0 = time.time()
        p = subprocess.Popen(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        text = p.stdout.read()
        _, status, ru = os.wait4(p.pid, 0)
        dt = time.time() - t0
        rc = os.waitstatus_to_exitcode(status)
        err = [l for l in text.splitlines() if 'error' in l.lower()]
        return name, dt, ru.ru_maxrss, rc, err[:3]

    measured, over = {}, []
    running_mb = 0.0
    log = open(args.log, 'w')
    t_start = time.time()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            ready = [m for m in pending if deps[m] <= done and not (deps[m] & set(failed))]
            ready.sort(key=lambda m: -cp[m])
            for m in admit(ready, len(running), running_mb, args.jobs, budget_mb, mb):
                pending.discard(m)
                running_mb += mb(m)
                running[pool.submit(run, m, mods[m])] = m
            if not running:
                break
            fin, _ = wait(list(running), return_when=FIRST_COMPLETED)
            for fut in fin:
                m = running.pop(fut)
                running_mb -= mb(m)
                name, dt, peak, rc, err = fut.result()
                done.add(name)
                peak_mb = peak // 1024
                if rc == 0:
                    measured[name] = (dt, peak_mb)
                    if peak_mb > mb(name) * DRIFT:
                        over.append(name)
                line = f'{name} {dt:.1f}s {peak_mb}MB rc={rc}' + (' ' + ' | '.join(err) if err else '')
                print(line, flush=True); log.write(line + '\n'); log.flush()
                if rc != 0:
                    failed.append(name)
    wall = time.time() - t_start
    save_profile(args.save_profile, prof, measured)
    if over:
        print(f'warning: {len(over)} modules exceeded their predicted peak by over '
              f'{int((DRIFT - 1) * 100)}% (table updated)', file=sys.stderr)
    summary = (f'WALL {wall:.0f}s modules {len(done)} failed {len(failed)} skipped {len(pending)} '
               f'jobs {args.jobs} memory {args.memory:.0f}GB')
    print(summary, flush=True); log.write(summary + '\n')
    return 1 if failed or pending else 0


if __name__ == '__main__':
    sys.exit(main())
