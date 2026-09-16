import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 73 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3938_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3933l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3938_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3933l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3938_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3933l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3938_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3933l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3938_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3933l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3938_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3933l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3938 :
    hubcapFit theRedpart rf7 p7_3933l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3938_1, c7_3938_2, c7_3938_3, c7_3938_4, c7_3938_5, c7_3938_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3939_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3932l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3939_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3932l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3939_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3932l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3939_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3932l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3939_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3932l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3939_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3932l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3939_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3932l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3939 :
    hubcapFit theRedpart rf7 p7_3932l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3939_1, c7_3939_2, c7_3939_3, c7_3939_4, c7_3939_5, c7_3939_6, c7_3939_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3941_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3931l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3941_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3931l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3941_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3931l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3941_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3931l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3941_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3931l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3941_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3931l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3941 :
    hubcapFit theRedpart rf7 p7_3931l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3941_1, c7_3941_2, c7_3941_3, c7_3941_4, c7_3941_5, c7_3941_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3942_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3930l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3942_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3930l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3942_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3930l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3942_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3930l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3942_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3930l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3942_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3930l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3942 :
    hubcapFit theRedpart rf7 p7_3930l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3942_1, c7_3942_2, c7_3942_3, c7_3942_4, c7_3942_5, c7_3942_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3944_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3929l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3944_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3929l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3944_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3929l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3944_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3929l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3944_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3929l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3944_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3929l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3944 :
    hubcapFit theRedpart rf7 p7_3929l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3944_1, c7_3944_2, c7_3944_3, c7_3944_4, c7_3944_5, c7_3944_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3945_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3928l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3945_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3928l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3945_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3928l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3945_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3928l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3945_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3928l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3945_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3928l) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3945 :
    hubcapFit theRedpart rf7 p7_3928l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3945_1, c7_3945_2, c7_3945_3, c7_3945_4, c7_3945_5, c7_3945_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3947_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3927l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3947_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3927l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3947_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3927l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3947_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3927l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3947_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3927l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3947 :
    hubcapFit theRedpart rf7 p7_3927l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3947_1, c7_3947_2, c7_3947_3, c7_3947_4, c7_3947_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3948_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3926l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3948_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3926l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3948_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3926l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3948_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3926l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3948_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3926l) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3948_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3926l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3948_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3926l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3948 :
    hubcapFit theRedpart rf7 p7_3926l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3948_1, c7_3948_2, c7_3948_3, c7_3948_4, c7_3948_5, c7_3948_6, c7_3948_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3950_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3925l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3950_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3925l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3950_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3925l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3950_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3925l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3950_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3925l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3950 :
    hubcapFit theRedpart rf7 p7_3925l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3950_1, c7_3950_2, c7_3950_3, c7_3950_4, c7_3950_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3951_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3924l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3951_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3924l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3951_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3924l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3951_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3924l) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3951_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3924l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3951 :
    hubcapFit theRedpart rf7 p7_3924l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3951_1, c7_3951_2, c7_3951_3, c7_3951_4, c7_3951_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3953_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3923l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3953_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3923l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3953_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3923l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3953_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3923l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3953_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3923l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3953_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3923l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3953 :
    hubcapFit theRedpart rf7 p7_3923l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3953_1, c7_3953_2, c7_3953_3, c7_3953_4, c7_3953_5, c7_3953_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3954_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3922l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3954_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3922l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3954_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3922l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3954_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3922l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3954_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3922l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3954_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3922l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3954 :
    hubcapFit theRedpart rf7 p7_3922l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3954_1, c7_3954_2, c7_3954_3, c7_3954_4, c7_3954_5, c7_3954_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3956_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3921l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3956_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3921l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3956_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3921l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3956_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3921l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3956_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3921l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3956_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3921l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3956 :
    hubcapFit theRedpart rf7 p7_3921l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3956_1, c7_3956_2, c7_3956_3, c7_3956_4, c7_3956_5, c7_3956_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3966_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3965r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3966_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3965r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3966_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3965r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3966_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3965r) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3966_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3965r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3966 :
    hubcapFit theRedpart rf7 p7_3965r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3966_1, c7_3966_2, c7_3966_3, c7_3966_4, c7_3966_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3967_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3967_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3965l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3967_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3967_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3965l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3967_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3965l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3967_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3965l) (hubSubn 7 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3967_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3965l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3967 :
    hubcapFit theRedpart rf7 p7_3965l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3967_1, c7_3967_2, c7_3967_3, c7_3967_4, c7_3967_5, c7_3967_6, c7_3967_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3972_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3971r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3972_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3971r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3972_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3971r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3972_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3971r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3972_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3971r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3972_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3971r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3972 :
    hubcapFit theRedpart rf7 p7_3971r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3972_1, c7_3972_2, c7_3972_3, c7_3972_4, c7_3972_5, c7_3972_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3973_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3971l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3973_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3973_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3971l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3973_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3971l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3973_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3971l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3973_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3971l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3973 :
    hubcapFit theRedpart rf7 p7_3971l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3973_1, c7_3973_2, c7_3973_3, c7_3973_4, c7_3973_5, c7_3973_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3975_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3969l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3975_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3975_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3969l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3975_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3969l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3975_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3969l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3975_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3969l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3975 :
    hubcapFit theRedpart rf7 p7_3969l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3975_1, c7_3975_2, c7_3975_3, c7_3975_4, c7_3975_5, c7_3975_6]

end FourColor
