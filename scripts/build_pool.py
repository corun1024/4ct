#!/usr/bin/env python3
"""Build the `FourColor` modules with a fixed number of parallel `lean` processes.

Lake starts as many jobs as the machine has hardware threads and offers no way
to say fewer, which makes a build on many cores memory-bandwidth-bound and a
build pinned to a few cores thrash.  This runs the same `lean` invocations Lake
would, in dependency order, but never more than `--jobs` at a time, and prints
each module's wall time and peak memory.  It writes the same `.olean`/`.ilean`
files into `.lake/build`, so a following `lake build` has nothing left to do
but refresh its traces.

It is incremental: a module whose `.olean` is newer than its source and than
every dependency's `.olean` is skipped.  `--clean` rebuilds everything.

Usage (from the project root, after `lake exe cache get` and a build of the
dependencies): scripts/build_pool.py --jobs N [--clean] [--log FILE]
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


def uptodate(name, path, deps, mods):
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


def run(name, path, env, root):
    out = os.path.join('.lake/build/lib/lean', name.replace('.', '/'))
    os.makedirs(os.path.dirname(out), exist_ok=True)
    cmd = ['lean', '-R', root] + LEAN_OPTS + ['-o', out + '.olean', '-i', out + '.ilean', path]
    t0 = time.time()
    p = subprocess.Popen(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    out = p.stdout.read()
    _, status, ru = os.wait4(p.pid, 0)
    dt = time.time() - t0
    rc = os.waitstatus_to_exitcode(status)
    err = [l for l in out.splitlines() if 'error' in l.lower()]
    return name, dt, ru.ru_maxrss, rc, err[:3]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--clean', action='store_true', help='rebuild every FourColor module')
    ap.add_argument('--log', default='build_pool.log')
    args = ap.parse_args()
    root = os.getcwd()
    env = dict(os.environ)
    env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True,
                                      text=True, check=True).stdout.strip()
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
    if args.clean:
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
                if deps[m] <= done and uptodate(m, mods[m], deps[m], mods):
                    pending.discard(m); done.add(m); progress = True
        if done:
            print(f'up to date: {len(done)} modules; {len(pending)} to build', flush=True)
    log = open(args.log, 'w')
    t_start = time.time()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            ready = [m for m in pending if deps[m] <= done and not (deps[m] & set(failed))]
            # largest dependency fan-out first keeps the pool busy
            ready.sort(key=lambda m: -sum(1 for d in deps.values() if m in d))
            while ready and len(running) < args.jobs:
                m = ready.pop(0); pending.discard(m)
                running[pool.submit(run, m, mods[m], env, root)] = m
            if not running:
                break
            fin, _ = wait(list(running), return_when=FIRST_COMPLETED)
            for fut in fin:
                m = running.pop(fut)
                name, dt, peak, rc, err = fut.result()
                done.add(name)
                line = f'{name} {dt:.1f}s {peak // 1024}MB rc={rc}' + (' ' + ' | '.join(err) if err else '')
                print(line, flush=True); log.write(line + '\n'); log.flush()
                if rc != 0:
                    failed.append(name)
    wall = time.time() - t_start
    print(f'WALL {wall:.0f}s modules {len(done)} failed {len(failed)} skipped {len(pending)} jobs {args.jobs}', flush=True)
    log.write(f'WALL {wall:.0f}s modules {len(done)} failed {len(failed)} skipped {len(pending)} jobs {args.jobs}\n')
    return 1 if failed or pending else 0


if __name__ == '__main__':
    sys.exit(main())
