# The Four Colour Theorem in Lean 4

A formalisation of the Four Colour Theorem in Lean 4 / Mathlib, following the
structure of Georges Gonthier and Benjamin Werner's Coq proof
([rocq-community/fourcolor](https://github.com/rocq-community/fourcolor)) but
written idiomatically for Mathlib rather than transliterated from MathComp.

## Status

**The theorem is proved.**  `FourColor.fourColorTheorem : FourColorTheorem`
builds, and `scripts/check.sh` verifies that it depends only on `propext`,
`Classical.choice` and `Quot.sound`, with no `sorry`, no `native_decide` and no
extra axiom anywhere in the 115 000 declarations of the development.  The
statement (`FourColor/RealPlane.lean`) is Gonthier's, clause for clause, over
Mathlib's reals; `FourColor/RealPlaneMathlib.lean` identifies its elementary
topology with Mathlib's.  `scripts/Audit.lean` adds negative controls — every
decision procedure the proof relies on is shown to answer `false` somewhere —
so that the checks cannot have degenerated into tautologies.
[scripts/README.md](scripts/README.md) describes how the computational
certificates are generated.

## Approach

The Coq development is built on MathComp's `seq`/`fintype`/boolean-reflection
idiom. Rather than port that idiom, each notion is expressed with the Mathlib
structure it actually is, so that Mathlib's lemmas replace hand-rolled ones:

| Reference (`color.v`, …)        | Here                                              |
| ------------------------------- | ------------------------------------------------- |
| `color` with `addc`, `addcA`, … | `Color` with an `AddCommGroup` instance (Klein four-group) |
| `edge_perm`, `permc`, `inv_eperm` | `EdgePerm` with a `Group` instance acting by additive automorphisms |
| `sumt` (`foldr addc Color0`)    | `List.sum`                                        |
| `trace` and its `rot`/`rev` laws | `trace l = zipWith (+) l (l.rotate 1)`, then Mathlib's rotate/reverse API |
| `seq`, `rot`, `rev`             | `List`, `List.rotate`, `List.reverse`             |
| boolean reflection (`reflect`)  | `Prop` with `Decidable` instances, `decide`       |
| `hypermap` (three `permutation`s) | `Hypermap` with three `Equiv.Perm` fields         |
| `cedge`/`cnode`/`cface`         | `Equiv.Perm.SameCycle` of the respective permutation |
| `fcard f` (orbit count)         | `Nat.card (Quotient (SameCycle.setoid f))`        |
| `order f x`, `arity`            | `Function.minimalPeriod`                          |
| `simple` (via face roots)       | `List.Pairwise (fun x y => ¬ CFace x y)`          |
| `decide_ring_trace` (an enumeration) | `Fintype.decidableExistsFintype` — colourings of a finite dart type form a finite type |

Some proofs come out shorter than the reference's because the Mathlib
structure does the work. Multiplying a permutation by a transposition changes
its orbit count by one, with **parity** — already pinned down by
`Equiv.Perm.sign` — deciding the direction; that single fact replaces the
reference's hand decomposition of the orbit count over two edge cycles, and it
is what makes the Walkup construction and the Euler formula fall out.

Two results are deliberately **not** ported, because nothing in the development
uses them: `Jordan_planar` and `Jordan_WalkupE`, the converse direction of the
planarity equivalence. Every use of planarity is `planar → Jordan`, which is
proved.

Finite brute-force facts that the reference proves with `by do 3!case` are
discharged by `decide`, kernel-checked.

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
FourColor/EulerTree.lean the graph-theoretic core of Euler's formula (in progress)
FourColor/Geometry.lean  bridges, arity, face bands, rings, plain/cubic maps
FourColor/Coloring.lean  colourings, minimal counter-examples, contracts
FourColor/Cube.lean      six copies of each dart: a plain cubic map
FourColor/Patch.lean     cutting a map in two along a ring
FourColor/Sew.lean       glueing two maps along a common border
FourColor/Snip.lean      the disk a ring delimits
FourColor/Kempe.lean     chromogram surgery for Kempe closure
FourColor/CfMap.lean     configuration programs and the maps they build
FourColor/Configurations.lean  the 633 reducible configurations
FourColor/Quiz.lean      question trees that locate a configuration
FourColor/Part.lean      second-neighbourhood descriptions for discharging
FourColor/Chromogram.lean, Ctree.lean, Gtree.lean, Dyck.lean,
FourColor/InitCtree.lean, InitGtree.lean, CtreeRestrict.lean,
FourColor/GtreeRestrict.lean   the reducibility engine
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
                         the chromogram walk over a universe of traces, proved sound
FourColor/Bulk/          Kempe closure as bit-operations over all traces of a ring
FourColor/Bulk/Cfg/      the 633 reducibility certificates (generated)
FourColor/Mask/          the residual walks of 110 configurations (generated)
FourColor/Reduce/All.lean, Complete.lean   the certificates chained; the theorem
```

## Building

```shell
./build.sh             # or JOBS=8 ./build.sh to pin the parallelism
```

That is the whole thing: Mathlib from the build cache, the reducibility
certificates regenerated from `FourColor/Configurations.lean` if they are not
already present, every module built, then `scripts/check.sh` — no sorries, no
extra axioms, and the anti-vacuity controls.  It prints

```
THEOREM PROVED: FourColor.fourColorTheorem depends only on [propext, Classical.choice, Quot.sound]
```

Every step is a no-op when it has nothing left to do, so the command can be
re-run after an interruption.  The build is a kernel check of about 900 modules
of computation; the largest single module peaks at 8.3 GB, which is what bounds
how many jobs fit at once.  It comes to about 11 core-hours: measured at 2 h
46 min on four cores and 29.5 min on 32.  Half of that is the unavoidability
presentations, the rest the reducibility certificates; the largest single
module is the residual walk of configuration 562, at 13 minutes.

## Licence

MIT (see `LICENSE`).  Copyright (c) 2026 Chris Emery.

This development follows the structure of the Coq proof of the Four Colour
Theorem by Georges Gonthier and Benjamin Werner
([rocq-community/fourcolor](https://github.com/rocq-community/fourcolor)),
distributed under the
[CeCILL-B](https://cecill.info/licences/Licence_CeCILL-B_V1-en.html) licence,
whose article 5.3.2 allows a derived work to carry a different licence so long
as the credits of its article 5.3.4 are given.  No Coq source text is copied
here, but three kinds of data are mechanical translations of it and are
credited in their headers: `FourColor/Configurations.lean` (from
`configurations.v`), the presentation scripts `FourColor/Present*.lean` (from
`present*.v`), and the quiz data computed from the configurations.  That credit
is in `LICENSE` and must be kept in any redistribution.  Reference: G.
Gonthier, *Formal Proof — The Four-Color Theorem*, Notices of the AMS 55 (11),
2008; the `fourcolor` Rocq library, CeCILL-B.
