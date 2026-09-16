import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 55 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2987_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2975l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2987_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2975l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2987_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2975l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2987_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2975l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2987_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2975l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2987_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2975l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2987_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2975l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2987 :
    hubcapFit theRedpart rf7 p7_2975l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2987_1, c7_2987_2, c7_2987_3, c7_2987_4, c7_2987_5, c7_2987_6, c7_2987_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2989_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2974l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2989_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2974l) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2989_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2974l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2989_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2974l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2989 :
    hubcapFit theRedpart rf7 p7_2974l
    (Hubcap.one 6 0 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2989_1, c7_2989_2, c7_2989_3, c7_2989_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2990_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2973l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2990_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2973l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2990_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2973l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2990_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2973l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2990_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2973l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2990_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2973l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2990 :
    hubcapFit theRedpart rf7 p7_2973l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2990_1, c7_2990_2, c7_2990_3, c7_2990_4, c7_2990_5, c7_2990_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2992_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2972l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2992_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2972l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2992_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2972l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2992_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2972l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2992_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2972l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2992 :
    hubcapFit theRedpart rf7 p7_2972l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2992_1, c7_2992_2, c7_2992_3, c7_2992_4, c7_2992_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2994_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2951l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2994_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2951l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2994_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2951l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2994_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2951l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2994_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2951l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2994_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2951l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2994 :
    hubcapFit theRedpart rf7 p7_2951l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2994_1, c7_2994_2, c7_2994_3, c7_2994_4, c7_2994_5, c7_2994_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2995_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2950l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2995_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2950l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2995_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2950l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2995_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2950l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2995_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2950l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2995 :
    hubcapFit theRedpart rf7 p7_2950l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2995_1, c7_2995_2, c7_2995_3, c7_2995_4, c7_2995_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3016_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3015r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3016_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3015r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3016_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3015r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3016_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3015r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3016_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3015r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3016_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3015r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3016 :
    hubcapFit theRedpart rf7 p7_3015r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3016_1, c7_3016_2, c7_3016_3, c7_3016_4, c7_3016_5, c7_3016_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3017_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3015l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3017_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3015l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3017_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3015l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3017_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3015l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3017_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3015l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3017_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3015l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3017 :
    hubcapFit theRedpart rf7 p7_3015l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3017_1, c7_3017_2, c7_3017_3, c7_3017_4, c7_3017_5, c7_3017_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3019_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3014l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3019_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3014l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3019_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3014l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3019_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3014l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3019_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3014l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3019_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3014l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3019_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3014l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3019 :
    hubcapFit theRedpart rf7 p7_3014l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3019_1, c7_3019_2, c7_3019_3, c7_3019_4, c7_3019_5, c7_3019_6, c7_3019_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3021_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3012l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3021_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3012l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3021_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3012l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3021_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3012l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3021_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3012l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3021_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3012l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3021 :
    hubcapFit theRedpart rf7 p7_3012l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3021_1, c7_3021_2, c7_3021_3, c7_3021_4, c7_3021_5, c7_3021_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3023_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3011l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3023_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3011l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3023_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3011l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3023_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3011l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3023_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3011l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3023_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3011l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3023 :
    hubcapFit theRedpart rf7 p7_3011l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3023_1, c7_3023_2, c7_3023_3, c7_3023_4, c7_3023_5, c7_3023_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3029_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3028r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3029_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3028r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3029_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3028r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3029_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3028r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3029_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3028r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3029_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3028r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3029 :
    hubcapFit theRedpart rf7 p7_3028r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3029_1, c7_3029_2, c7_3029_3, c7_3029_4, c7_3029_5, c7_3029_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3030_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3028l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3030_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3028l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3030_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3028l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3030_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3028l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3030_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3028l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3030_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3028l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3030 :
    hubcapFit theRedpart rf7 p7_3028l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3030_1, c7_3030_2, c7_3030_3, c7_3030_4, c7_3030_5, c7_3030_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3032_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3027l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3032_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3027l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3032_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3027l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3032_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3027l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3032_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3027l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3032_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3027l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3032 :
    hubcapFit theRedpart rf7 p7_3027l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3032_1, c7_3032_2, c7_3032_3, c7_3032_4, c7_3032_5, c7_3032_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3033_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3026l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3033_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3026l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3033_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3026l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3033_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3026l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3033_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3026l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3033_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3026l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3033_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3026l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3033 :
    hubcapFit theRedpart rf7 p7_3026l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3033_1, c7_3033_2, c7_3033_3, c7_3033_4, c7_3033_5, c7_3033_6, c7_3033_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3035_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3025l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3035_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3025l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3035_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3025l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3035_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3025l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3035_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3025l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3035_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3025l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3035_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3025l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3035 :
    hubcapFit theRedpart rf7 p7_3025l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3035_1, c7_3035_2, c7_3035_3, c7_3035_4, c7_3035_5, c7_3035_6, c7_3035_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3037_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3024l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3037_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3024l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3037_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3037_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3024l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3037_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3037_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3024l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3037 :
    hubcapFit theRedpart rf7 p7_3024l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3037_1, c7_3037_2, c7_3037_3, c7_3037_4, c7_3037_5, c7_3037_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3039_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3008l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3039_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3008l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3039_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3008l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3039_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3008l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3039_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3008l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3039 :
    hubcapFit theRedpart rf7 p7_3008l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3039_1, c7_3039_2, c7_3039_3, c7_3039_4, c7_3039_5]

end FourColor
