import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 19 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_891_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_891_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_871l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_891_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_891_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_891_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_891_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_891_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_891_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_891_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_871l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_891 :
    hubcapFit theRedpart rf10 p10_871l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_891_1, c10_891_2, c10_891_3, c10_891_4, c10_891_5, c10_891_6, c10_891_7, c10_891_8, c10_891_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_893_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_870l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_893_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_870l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_893_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_870l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_893_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_870l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_893_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_870l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_893_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_870l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_893_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_870l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_893_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_870l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_893_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_870l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_893 :
    hubcapFit theRedpart rf10 p10_870l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_893_1, c10_893_2, c10_893_3, c10_893_4, c10_893_5, c10_893_6, c10_893_7, c10_893_8, c10_893_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_895_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_868l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_895_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_868l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_895_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_868l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_895_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_868l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_895_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_868l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_895_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_868l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_895_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_868l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_895_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_868l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_895_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_868l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_895 :
    hubcapFit theRedpart rf10 p10_868l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_895_1, c10_895_2, c10_895_3, c10_895_4, c10_895_5, c10_895_6, c10_895_7, c10_895_8, c10_895_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_897_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_897_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_897_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_897_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_865l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_897_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_897_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_865l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_897_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_897_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_897_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_865l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_897 :
    hubcapFit theRedpart rf10 p10_865l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_897_1, c10_897_2, c10_897_3, c10_897_4, c10_897_5, c10_897_6, c10_897_7, c10_897_8, c10_897_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_899_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_864l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_899_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_864l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_899_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_864l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_899_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_864l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_899_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_864l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_899_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_864l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_899_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_864l) (hubSubn 10 5 3) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_899_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_864l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_899 :
    hubcapFit theRedpart rf10 p10_864l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 9 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_899_1, c10_899_2, c10_899_3, c10_899_4, c10_899_5, c10_899_6, c10_899_7, c10_899_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_901_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_863l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_901_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_863l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_901_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_863l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_901_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_863l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_901_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_863l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_901_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_863l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_901_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_863l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_901_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_863l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_901_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_863l) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_901 :
    hubcapFit theRedpart rf10 p10_863l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_901_1, c10_901_2, c10_901_3, c10_901_4, c10_901_5, c10_901_6, c10_901_7, c10_901_8, c10_901_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_903_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_903_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_852l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_903_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_903_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_852l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_903_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_903_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_852l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_903_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_903_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_852l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_903_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_852l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_903 :
    hubcapFit theRedpart rf10 p10_852l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_903_1, c10_903_2, c10_903_3, c10_903_4, c10_903_5, c10_903_6, c10_903_7, c10_903_8, c10_903_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_905_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_851l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_905_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_851l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_905_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_851l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_905_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_851l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_905_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_851l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_905_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_851l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_905_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_851l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_905_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_851l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_905_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_851l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_905 :
    hubcapFit theRedpart rf10 p10_851l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_905_1, c10_905_2, c10_905_3, c10_905_4, c10_905_5, c10_905_6, c10_905_7, c10_905_8, c10_905_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_850l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_850l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_850l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_850l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_907_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_850l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_907 :
    hubcapFit theRedpart rf10 p10_850l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_907_1, c10_907_2, c10_907_3, c10_907_4, c10_907_5, c10_907_6, c10_907_7, c10_907_8, c10_907_9, c10_907_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_849l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_849l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_849l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_849l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_849l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_849l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_849l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_849l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_849l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_909_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_849l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_909 :
    hubcapFit theRedpart rf10 p10_849l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_909_1, c10_909_2, c10_909_3, c10_909_4, c10_909_5, c10_909_6, c10_909_7, c10_909_8, c10_909_9, c10_909_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_911_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_848l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_911_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_848l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_911_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_848l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_911_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_848l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_911_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_848l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_911_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_848l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_911_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_848l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_911_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_848l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_911_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_848l) (hubSubn 10 9 8) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_911 :
    hubcapFit theRedpart rf10 p10_848l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_911_1, c10_911_2, c10_911_3, c10_911_4, c10_911_5, c10_911_6, c10_911_7, c10_911_8, c10_911_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_913_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_847l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_913_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_847l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_913_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_847l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_913_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_847l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_913_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_847l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_913_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_847l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_913_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_847l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_913_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_847l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_913_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_847l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_913 :
    hubcapFit theRedpart rf10 p10_847l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_913_1, c10_913_2, c10_913_3, c10_913_4, c10_913_5, c10_913_6, c10_913_7, c10_913_8, c10_913_9]

end FourColor
