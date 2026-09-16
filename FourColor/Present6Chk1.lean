import FourColor.Present6Defs
import FourColor.TheQuizTree

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 1 of the arity 6 presentation

One of 8 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_25_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_24r) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_25_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_24r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_25_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_24r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_25 :
    hubcapFit theRedpart rf6 p6_24r
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_25_1, c6_25_2, c6_25_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_28_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_19l) (hubSubn 6 5 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_28_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_19l) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_28_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_19l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_28 :
    hubcapFit theRedpart rf6 p6_19l
    (Hubcap.two 0 5 2 <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_28_1, c6_28_2, c6_28_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_41_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_40r) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_41_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_40r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_41_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_40r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_41 :
    hubcapFit theRedpart rf6 p6_40r
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_41_1, c6_41_2, c6_41_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_43_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_42r) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_43_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_42r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_43_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_42r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_43 :
    hubcapFit theRedpart rf6 p6_42r
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_43_1, c6_43_2, c6_43_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_44_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_42l) (hubSubn 6 5 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_44_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_42l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_44_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_42l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_44 :
    hubcapFit theRedpart rf6 p6_42l
    (Hubcap.two 0 5 (-2) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_44_1, c6_44_2, c6_44_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_47_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_37l) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_47_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_37l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_47_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_37l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_47 :
    hubcapFit theRedpart rf6 p6_37l
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_47_1, c6_47_2, c6_47_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_51_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_50r) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_51_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_50r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_51_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_50r) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_51 :
    hubcapFit theRedpart rf6 p6_50r
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_51_1, c6_51_2, c6_51_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_52_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_50l) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_52_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_50l) (hubSubn 6 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_52_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_50l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_52 :
    hubcapFit theRedpart rf6 p6_50l
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_52_1, c6_52_2, c6_52_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_54_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_49l) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_54_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_49l) (hubSubn 6 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_54_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_49l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_54 :
    hubcapFit theRedpart rf6 p6_49l
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_54_1, c6_54_2, c6_54_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_63_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_62r) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_63_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_62r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_63_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_62r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_63 :
    hubcapFit theRedpart rf6 p6_62r
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_63_1, c6_63_2, c6_63_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_64_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_62l) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_64_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_62l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_64_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_62l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_64 :
    hubcapFit theRedpart rf6 p6_62l
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_64_1, c6_64_2, c6_64_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_68_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_67r) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_68_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_67r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_68_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_67r) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_68 :
    hubcapFit theRedpart rf6 p6_67r
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_68_1, c6_68_2, c6_68_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_69_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_67l) (hubSubn 6 5 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_69_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_67l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_69_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_67l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_69 :
    hubcapFit theRedpart rf6 p6_67l
    (Hubcap.two 0 5 (-2) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_69_1, c6_69_2, c6_69_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_71_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_66l) (hubSubn 6 5 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_71_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_66l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_71_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_66l) (hubSubn 6 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_71 :
    hubcapFit theRedpart rf6 p6_66l
    (Hubcap.two 0 5 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_71_1, c6_71_2, c6_71_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_74_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_73r) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_74_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_73r) (hubSubn 6 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_74_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_73r) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_74 :
    hubcapFit theRedpart rf6 p6_73r
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_74_1, c6_74_2, c6_74_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_75_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_73l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_75_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_73l) (hubSubn 6 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_75_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_73l) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_75 :
    hubcapFit theRedpart rf6 p6_73l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_75_1, c6_75_2, c6_75_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_86_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_85r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_86_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_85r) (hubSubn 6 5 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_86_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_85r) (hubSubn 6 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_86 :
    hubcapFit theRedpart rf6 p6_85r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_86_1, c6_86_2, c6_86_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_87_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_85l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_87_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_85l) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_87_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_85l) (hubSubn 6 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_87 :
    hubcapFit theRedpart rf6 p6_85l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_87_1, c6_87_2, c6_87_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_91_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_90r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_91_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_90r) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_91_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_90r) (hubSubn 6 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_91 :
    hubcapFit theRedpart rf6 p6_90r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_91_1, c6_91_2, c6_91_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_92_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_90l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_92_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_90l) (hubSubn 6 5 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_92_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_90l) (hubSubn 6 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_92 :
    hubcapFit theRedpart rf6 p6_90l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 (-2) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_92_1, c6_92_2, c6_92_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_94_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_89l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_94_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_89l) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_94_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_89l) (hubSubn 6 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_94 :
    hubcapFit theRedpart rf6 p6_89l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_94_1, c6_94_2, c6_94_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_98_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_97r) (hubSubn 6 2 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_98_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_97r) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_98_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_97r) (hubSubn 6 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_98 :
    hubcapFit theRedpart rf6 p6_97r
    (Hubcap.two 0 2 1 <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_98_1, c6_98_2, c6_98_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_99_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_97l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_99_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_97l) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_99_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_97l) (hubSubn 6 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_99 :
    hubcapFit theRedpart rf6 p6_97l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_99_1, c6_99_2, c6_99_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_102_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_101r) (hubSubn 6 2 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_102_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_101r) (hubSubn 6 5 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_102_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_101r) (hubSubn 6 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_102 :
    hubcapFit theRedpart rf6 p6_101r
    (Hubcap.two 0 2 1 <|
     Hubcap.two 1 5 (-2) <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_102_1, c6_102_2, c6_102_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_103_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_101l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_103_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_101l) (hubSubn 6 5 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_103_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_101l) (hubSubn 6 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_103 :
    hubcapFit theRedpart rf6 p6_101l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 (-2) <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_103_1, c6_103_2, c6_103_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_111_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_110r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_111_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_110r) (hubSubn 6 5 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_111_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_110r) (hubSubn 6 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_111 :
    hubcapFit theRedpart rf6 p6_110r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_111_1, c6_111_2, c6_111_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_112_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_110l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_112_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_110l) (hubSubn 6 5 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_112_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_110l) (hubSubn 6 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_112 :
    hubcapFit theRedpart rf6 p6_110l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_112_1, c6_112_2, c6_112_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_115_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_114r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_115_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_114r) (hubSubn 6 5 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_115_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_114r) (hubSubn 6 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_115 :
    hubcapFit theRedpart rf6 p6_114r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_115_1, c6_115_2, c6_115_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_116_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_114l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_116_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_114l) (hubSubn 6 5 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_116_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_114l) (hubSubn 6 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_116 :
    hubcapFit theRedpart rf6 p6_114l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_116_1, c6_116_2, c6_116_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_120_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_119r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_120_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_119r) (hubSubn 6 5 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_120_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_119r) (hubSubn 6 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_120 :
    hubcapFit theRedpart rf6 p6_119r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 1 <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_120_1, c6_120_2, c6_120_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_121_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_119l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_121_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_119l) (hubSubn 6 5 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_121_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_119l) (hubSubn 6 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_121 :
    hubcapFit theRedpart rf6 p6_119l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 5 1 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_121_1, c6_121_2, c6_121_3]

end FourColor
