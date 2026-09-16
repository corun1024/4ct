# The Four Colour Theorem in Lean 4

A complete formalisation of the Four Colour Theorem in Lean 4 and Mathlib,
following the architecture of Georges Gonthier and Benjamin Werner's Coq proof
([rocq-community/fourcolor](https://github.com/rocq-community/fourcolor)).

```
THEOREM PROVED: FourColor.fourColorTheorem : FourColor.FourColorTheorem depends only on [propext, Classical.choice, Quot.sound]
checked 115342 FourColor declarations: no sorries, no extra axioms
anti-vacuity audit: negative controls pass
```

`FourColor.fourColorTheorem` depends on nothing beyond Lean's three standard
axioms. There is no `sorry`, no `axiom`, no `native_decide`, and no
`partial`, `unsafe` or `opaque` definition anywhere in the development.
`scripts/check.sh` enforces all of that on every build.

The statement lives in `FourColor/RealPlane.lean` and is Gonthier's, clause for
clause: a map is a partial equivalence relation on points of ℝ², a simple map
has open connected classes, and a four-colouring is a coarser map that
separates regions sharing a non-corner border point. Coq had to build the
reals from Dedekind cuts, because its logic has no quotients. Here ℝ is
Mathlib's, and `FourColor/RealPlaneMathlib.lean` proves the statement's
elementary topology agrees with Mathlib's `IsOpen`, `closure` and
`IsPreconnected`, so it can be read in either vocabulary.

## AI disclosure

This development was written with heavy use of AI. Claude Fable 5.1 produced
essentially all of it: the Lean proofs, the certificate engines in `tools/`,
and the generators in `scripts/`. The repository layout and the build tooling
were done with Claude Opus 5.

Due to heavy AI use, please do not take the theorem on the author's authority,
or the model's. Read the statement and run the checker. See next section.

Non-enterprise Claude Max subscriptions are heavily subsidised, so this did not
cost me personally more than $200. But Claude reports that if the API were used
directly, then the token cost would have been around $5k.

## Auditing the statement

Checking that a formal proof proves the right thing means reading its
statement, not its proof. That reading is deliberately small here.

`FourColor/RealPlane.lean` is 195 lines and imports three Mathlib topology
modules and nothing else — no module of this development. The transitive
dependency closure of `FourColorTheorem` touches 943 constants, of which 28
belong to this repository, and all 28 are defined in that one file: `Point`,
`Region`, `PlaneMap`, `Rect`, `IsOpenRegion`, `regionClosure`,
`IsConnectedRegion`, `PlainMap`, `SimpleMap`, `cover`, `border`, `notCorner`,
`Adjacent`, `Coloring`, `ColorableWith`, `FourColorTheorem`, and their
constructors and projections. The remaining 915 are Lean core and Mathlib,
mostly the construction of `Real`.

So to audit this:

1. Read `FourColor/RealPlane.lean` and satisfy yourself the statement is the
   Four Colour Theorem. Its three elementary topological notions are each
   proved to be Mathlib's: `isOpenRegion_iff` and `regionClosure_eq` in that
   file, and `isConnectedRegion_iff_isPreconnected` in
   `FourColor/RealPlaneMathlib.lean`, which also gives `simpleMap_iff` —
   the theorem's whole hypothesis restated as `PlainMap m ∧ (∀ z, IsOpen (m z))
   ∧ ∀ z, IsPreconnected (m z)`.
2. Confirm `FourColor.fourColorTheorem : FourColorTheorem` in
   `FourColor/Complete.lean`.
3. Run `./build.sh` and read its last three lines.

## Building

```shell
./build.sh
```

That does everything: fetches Mathlib from the build cache, regenerates the
reducibility certificates if they are absent, builds all 821 modules, then runs
the axiom and anti-vacuity checks. Each step is a no-op when it has nothing
left to do, so you can re-run it after an interruption.

You need [elan](https://github.com/leanprover/elan) (the toolchain in
`lean-toolchain` is fetched automatically), `gcc` and `python3`.

Cost on a 64-thread machine with 94 GB of RAM: a few minutes to regenerate the
certificates, then 7.5 core-hours of kernel work, which comes out at about 40
minutes wall clock. `JOBS=8 MEMORY=40 ./build.sh` overrides the defaults.

Where the work goes:

| | modules | core-hours |
| --- | ---: | ---: |
| discharging presentations | 406 | 3.9 |
| reducibility certificates | 349 | 3.5 |
| the mathematics | 65 | 0.1 |

The mathematics is nearly free. Everything else is the kernel checking
computations.

## The build system

Lake starts one job per hardware thread and offers no way to ask for fewer.
That is the wrong policy here, because the memory profile of this development
is extremely uneven. Measured across all 821 modules the median peak is
2.7 GB, but the p99 is 11.4 GB and `Bulk/Cfg/Hyb218B` alone peaks at 20.1 GB.
Eight modules exceed 12 GB. Running 64 of those concurrently exhausts 94 GB.

So `scripts/build_pool.py` issues the same `lean` invocations Lake would, under
two limits: at most `--jobs` processes (default `min(32, 90% of cores)`), and
never admitting a module whose predicted peak would push the total past
`--memory` (default 75% of available). Predictions come from
`scripts/module_cost.tsv`, a committed table of per-module wall time and peak
RSS. Peak memory transfers across machines; times do not, but only their
ratios matter, so a first build on unfamiliar hardware still schedules well.

Ready modules start in order of *critical path* — a module's own time plus the
longest chain of modules waiting on it — rather than in dependency order, so
the long poles start early. A module that does not fit the remaining budget is
skipped over in favour of one that does, instead of idling the machine behind
it. `--dry-run` prints the plan and predicted makespan without building,
which is how to find the point where more jobs stop helping. On the machine
above that point is around 16 jobs; the critical path puts a floor of 13
minutes on any amount of parallelism.

The cost table is only a hint. The dependency graph is parsed afresh from the
sources on every run, so a stale or missing table costs packing quality and
nothing else. Unprofiled modules are assumed to need 4 GB and the run says so.

One consequence worth knowing: Lake tracks its own trace files and knows
nothing about the oleans this writes, so `lake build` will rebuild the entire
development rather than adopt them. Build with `./build.sh`.

## What differs from the Coq proof

The mathematics is Gonthier and Werner's. The same reduction to finite planar
hypermaps, the same 633 reducible configurations, the same seven discharging
presentations covering hub arities five to eleven. What differs is how it is
expressed, and above all how the computational parts are checked.

### Idiomatic Mathlib, not transliterated MathComp

The Coq proof is written in MathComp's `seq`/`fintype`/boolean-reflection
style. Rather than port that style, each notion here is expressed as the
Mathlib structure it actually is, so Mathlib's lemmas replace hand-rolled ones:

| Reference | Here |
| --- | --- |
| `color` with `addc`, `addcA`, … | `Color` with an `AddCommGroup` instance (the Klein four-group) |
| `edge_perm`, `permc`, `inv_eperm` | `EdgePerm` with a `Group` instance acting by additive automorphisms |
| `sumt` (`foldr addc Color0`) | `List.sum` |
| `trace` and its `rot`/`rev` laws | `zipWith (+) l (l.rotate 1)`, then Mathlib's rotate/reverse API |
| `seq`, `rot`, `rev` | `List`, `List.rotate`, `List.reverse` |
| boolean reflection (`reflect`) | `Prop` with `Decidable` instances, `decide` |
| `hypermap` (three `permutation`s) | `Hypermap` with three `Equiv.Perm` fields |
| `cedge`/`cnode`/`cface` | `Equiv.Perm.SameCycle` of the respective permutation |
| `fcard f` (orbit count) | `Nat.card (Quotient (SameCycle.setoid f))` |
| `order f x`, `arity` | `Function.minimalPeriod` |
| `simple` (via face roots) | `List.Pairwise (fun x y => ¬ CFace x y)` |

Several proofs come out shorter because the structure does the work.
Multiplying a permutation by a transposition changes its orbit count by exactly
one, and `Equiv.Perm.sign` already decides the direction. That one fact
replaces the reference's hand decomposition of orbit counts over two edge
cycles, and it is what makes the Walkup construction and Euler's formula fall
out.

Two results are deliberately not ported, because nothing uses them:
`Jordan_planar` and `Jordan_WalkupE`, the converse direction of the
planarity–Jordan equivalence. Every use of planarity is `planar → Jordan`,
which is proved.

### The certificates, which is where the real deviation is

Coq settles reducibility by running a Kempe-chain closure program inside its
kernel, on a bytecode virtual machine added to Coq for this proof. Lean's
kernel has no such VM. The fast alternative, `native_decide`, means trusting
the compiler, which was ruled out. Everything here is `decide +kernel`.

Making that affordable meant redesigning the computation rather than the proof.
Lean's kernel costs roughly 10 µs per reduction step, but arithmetic on `Nat`
literals is GMP-accelerated, so a bitwise operation on a number several
megabits wide costs about what a handful of reduction steps cost. The whole
design falls out of that asymmetry:

**One number per trace set.** The ring colourings ("traces") of a ring of size
`n` become a single natural number with `3^(n-1)` bits. Kempe flips and colour
permutations are shift, and, or block moves on that number; ranks are
bit-sliced planes compared with bit-sliced adders. A certificate is checked by
about ninety wide operations per pair of chord positions, rather than one
search per colouring. This one-chord rule settles 523 of the 633
configurations outright, and its soundness — that it yields a Kempe co-closure
— is proved once, generically, in `FourColor/Bulk/`.

**A guided walk for the rest.** The remaining 110 configurations have residual
colourings whose justification needs several chords at once. Those are
certified by a walk over the chromograms carrying a bitmask over a small
universe of traces, pruned at every closed chord by the traces that chord
settles, with witnesses and rank levels supplied as data. Connecting the walk
to the bulk certificate needs a table of trace indices; computing it per trace
cost 15 ms each, so it is computed instead by a logarithmic-step bit spread, a
few hundred wide operations in total.

**A memory budget for discharging.** The discharging side follows the Coq
scripts, but every hubcap check is a kernel computation, and the kernel retains
every term a computation allocates until the declaration ends. A check of a few
thousand search steps costs gigabytes. So large hubcaps are split into finer
case analyses before emission — a hubcap valid on a part stays valid on a
refinement of it — each check is its own declaration, and `Elab.async` is
switched off in generated modules so declarations run one at a time and memory
is released between them.

The result: reducibility costs 3.5 core-hours. Evaluating the reference's
algorithm directly in the kernel was estimated at 90.

### Notes for Lean users

Things that cost real time to discover:

- The elaborator refuses `2^n` for `n` above 256 and then unfolds `Nat.pow`
  structurally. Any `show`, `simp` or `rfl` touching a width of 50,000 bits
  dies by recursion depth. Such lemmas are stated over a variable width and
  instantiated late.
- `theConfigs.length = 633` by `rfl` unfolds the literal. It has to be
  `decide +kernel`.
- A definition like `H := minPerm R` is recomputed by every declaration that
  uses it, so pair checks are grouped eight to a declaration.
- Whole-universe scans — a 13 s pass per rank level, times 116 levels — were
  replaced by explicit index lists.

### Reproducing the certificates

`FourColor/Bulk/Cfg/`, `FourColor/Mask/` and `FourColor/Reduce/All.lean` are
generated, and are not committed. `scripts/gen_certificates.sh` rebuilds them
from `FourColor/Configurations.lean` alone, deterministically: 62 bulk groups,
110 residual walks, 152 bridge modules. `build.sh` runs it when they are
missing.

None of that tooling is trusted. Every generated module is kernel-checked
against the soundness theorems in `FourColor/Bulk/` and `FourColor/Mask*.lean`,
and `scripts/Audit.lean` supplies negative controls showing that each checker
the proof relies on answers `false` somewhere — so a passing build cannot be a
decision procedure that accepts everything. See `scripts/README.md`.

## Layout

```
FourColor/Seq.lean       list primitives Mathlib lacks (pairmap, MathComp scanl)
FourColor/Path.lean      loop-cutting for paths (the reference's shortenP)
FourColor/Adjoin.lean    merging two classes of an equivalence
FourColor/Component.lean component counts under point deletion
FourColor/Orbit.lean     orbits of a permutation, as lists
FourColor/Color.lean     the four colours, edge permutations, edge traces
FourColor/Perm.lean      orbit counting; deleting a point from a permutation
FourColor/Hypermap.lean  hypermaps, genus, planarity, the Jordan condition
FourColor/Walkup.lean    the Walkup construction (dart deletion)
FourColor/Euler.lean     the Euler formula for hypermaps
FourColor/Jordan.lean    planarity implies the Jordan curve property
FourColor/EulerTree.lean the graph-theoretic core of Euler's formula
FourColor/Geometry.lean  bridges, arity, face bands, rings, plain/cubic maps
FourColor/Coloring.lean  colourings, minimal counter-examples, contracts
FourColor/Cube.lean      six copies of each dart: a plain cubic map
FourColor/Patch.lean     cutting a map in two along a ring
FourColor/Sew.lean       glueing two maps along a common border
FourColor/Snip.lean      the disk a ring delimits
FourColor/Kempe.lean     chromogram surgery for Kempe closure
FourColor/CfMap.lean     configuration programs and the maps they build
FourColor/Configurations.lean   the 633 reducible configurations
FourColor/Quiz.lean      question trees that locate a configuration
FourColor/Part.lean      second-neighbourhood descriptions for discharging
FourColor/Chromogram.lean, Ctree.lean, Gtree.lean, Dyck.lean, InitCtree.lean,
FourColor/InitGtree.lean, CtreeRestrict.lean, GtreeRestrict.lean
                         the reducibility engine
FourColor/Grid.lean      the integer grid as an infinite hypermap
FourColor/Matte.lean     grid regions with a contour, and their extensions
FourColor/RealPlane.lean the plane, and the statement of the theorem
FourColor/RealPlaneMathlib.lean  the statement's topology is Mathlib's
FourColor/Approx.lean    approximating the plane by grid squares
FourColor/Finitize.lean  the theorem reduces to finite maps
FourColor/Present*.lean  the seven unavoidability presentations (generated)
FourColor/CfReducible.lean, Cert.lean, CertBase.lean, CertFlip.lean
                         C-reducibility from a Kempe co-closure certificate
FourColor/MaskCert.lean, MaskRank.lean, MaskWit.lean, MaskChord.lean
                         the chromogram walk over a universe of traces
FourColor/Bulk/          Kempe closure as bit-operations over a ring's traces
FourColor/Bulk/Cfg/      the 633 reducibility certificates (generated)
FourColor/Mask/          the residual walks of 110 configurations (generated)
FourColor/Reduce/All.lean, Complete.lean   the certificates chained; the theorem
```

## Licence

MIT (see `LICENSE`). Copyright (c) 2026 Chris Emery.

This follows the structure of the Coq proof of the Four Colour Theorem by
Georges Gonthier and Benjamin Werner
([rocq-community/fourcolor](https://github.com/rocq-community/fourcolor)),
distributed under the
[CeCILL-B](https://cecill.info/licences/Licence_CeCILL-B_V1-en.html) licence,
whose article 5.3.2 allows a derived work to carry a different licence provided
the credits of article 5.3.4 are given. No Coq source text is copied here, but
three kinds of data are mechanical translations of it and say so in their
headers: `FourColor/Configurations.lean` (from `configurations.v`), the
presentation scripts `FourColor/Present*.lean` (from `present*.v`), and the
quiz data computed from the configurations. That credit is in `LICENSE` and
must be kept in any redistribution.

Reference: G. Gonthier, *Formal Proof — The Four-Color Theorem*, Notices of the
AMS 55 (11), 2008.
