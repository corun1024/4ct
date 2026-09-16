import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 19 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_885_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_885_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_885_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_885_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_885_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_885_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_846l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_885_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_846l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_885 :
    hubcapFit theRedpart rf9 p9_846l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_885_1, c9_885_2, c9_885_3, c9_885_4, c9_885_5, c9_885_6, c9_885_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_887_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_844l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_887_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_844l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_887_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_844l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_887_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_844l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_887_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_844l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_887_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_844l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_887_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_844l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_887 :
    hubcapFit theRedpart rf9 p9_844l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_887_1, c9_887_2, c9_887_3, c9_887_4, c9_887_5, c9_887_6, c9_887_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_889_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_842l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_889_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_842l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_889_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_842l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_889_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_842l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_889_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_842l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_889_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_842l) (hubSubn 9 8 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_889 :
    hubcapFit theRedpart rf9 p9_842l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_889_1, c9_889_2, c9_889_3, c9_889_4, c9_889_5, c9_889_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_891_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_891_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_891_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_891_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_891_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_841l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_891_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_841l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_891_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_891_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_891_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_891 :
    hubcapFit theRedpart rf9 p9_841l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_891_1, c9_891_2, c9_891_3, c9_891_4, c9_891_5, c9_891_6, c9_891_7, c9_891_8, c9_891_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_893_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_893_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_893_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_840l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_893_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_893_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_893_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_840l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_893_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_840l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_893 :
    hubcapFit theRedpart rf9 p9_840l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_893_1, c9_893_2, c9_893_3, c9_893_4, c9_893_5, c9_893_6, c9_893_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_895_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_895_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_895_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_839l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_895_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_895_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_895_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_839l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_895_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_839l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_895 :
    hubcapFit theRedpart rf9 p9_839l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_895_1, c9_895_2, c9_895_3, c9_895_4, c9_895_5, c9_895_6, c9_895_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_897_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_837l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_897_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_837l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_897_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_837l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_897_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_837l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_897_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_837l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_897_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_837l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_897_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_837l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_897 :
    hubcapFit theRedpart rf9 p9_837l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_897_1, c9_897_2, c9_897_3, c9_897_4, c9_897_5, c9_897_6, c9_897_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_899_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_835l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_899_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_835l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_899_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_835l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_899_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_835l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_899_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_835l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_899_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_835l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_899_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_835l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_899 :
    hubcapFit theRedpart rf9 p9_835l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_899_1, c9_899_2, c9_899_3, c9_899_4, c9_899_5, c9_899_6, c9_899_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_901_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_834l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_901_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_834l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_901_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_834l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_901_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_834l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_901_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_834l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_901_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_834l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_901_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_834l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_901 :
    hubcapFit theRedpart rf9 p9_834l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_901_1, c9_901_2, c9_901_3, c9_901_4, c9_901_5, c9_901_6, c9_901_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_903_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_833l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_903_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_833l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_903_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_833l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_903_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_833l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_903_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_833l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_903_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_833l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_903_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_833l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_903 :
    hubcapFit theRedpart rf9 p9_833l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_903_1, c9_903_2, c9_903_3, c9_903_4, c9_903_5, c9_903_6, c9_903_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_905_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_832l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_905_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_832l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_905_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_832l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_905_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_832l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_905_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_832l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_905_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_832l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_905 :
    hubcapFit theRedpart rf9 p9_832l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_905_1, c9_905_2, c9_905_3, c9_905_4, c9_905_5, c9_905_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_906_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_831l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_906_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_831l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_906_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_831l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_906_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_831l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_906_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_831l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_906_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_831l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_906_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_831l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_906_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_831l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_906_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_831l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_906 :
    hubcapFit theRedpart rf9 p9_831l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_906_1, c9_906_2, c9_906_3, c9_906_4, c9_906_5, c9_906_6, c9_906_7, c9_906_8, c9_906_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_908_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_830l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_908_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_830l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_908_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_830l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_908_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_830l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_908_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_830l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_908_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_830l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_908_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_830l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_908 :
    hubcapFit theRedpart rf9 p9_830l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_908_1, c9_908_2, c9_908_3, c9_908_4, c9_908_5, c9_908_6, c9_908_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_910_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_829l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_910_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_829l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_910_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_829l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_910_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_829l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_910_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_829l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_910_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_829l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_910_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_829l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_910 :
    hubcapFit theRedpart rf9 p9_829l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_910_1, c9_910_2, c9_910_3, c9_910_4, c9_910_5, c9_910_6, c9_910_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_912_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_828l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_912_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_828l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_912_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_828l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_912_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_912_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_912_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_912_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_912_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_912_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_912 :
    hubcapFit theRedpart rf9 p9_828l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_912_1, c9_912_2, c9_912_3, c9_912_4, c9_912_5, c9_912_6, c9_912_7, c9_912_8, c9_912_9]

end FourColor
