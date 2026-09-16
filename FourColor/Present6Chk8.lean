import FourColor.Present6Defs
import FourColor.TheQuizTree

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 8 of the arity 6 presentation

One of 8 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_662_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_652l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_662_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_652l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_662_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_652l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_662 :
    hubcapFit theRedpart rf6 p6_652l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_662_1, c6_662_2, c6_662_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_665_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_664r) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_665_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_664r) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_665_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_664r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_665 :
    hubcapFit theRedpart rf6 p6_664r
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_665_1, c6_665_2, c6_665_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_666_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_664l) (hubSubn 6 1 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_666_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_664l) (hubSubn 6 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_666_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_664l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_666 :
    hubcapFit theRedpart rf6 p6_664l
    (Hubcap.two 0 1 (-2) <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_666_1, c6_666_2, c6_666_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_668_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_663l) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_668_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_663l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_668_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_663l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_668 :
    hubcapFit theRedpart rf6 p6_663l
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_668_1, c6_668_2, c6_668_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_670_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_650l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_670_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_650l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_670_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_650l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_670 :
    hubcapFit theRedpart rf6 p6_650l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_670_1, c6_670_2, c6_670_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_673_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_672r) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_673_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_672r) (hubSubn 6 4 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_673_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_672r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_673 :
    hubcapFit theRedpart rf6 p6_672r
    (Hubcap.two 1 2 (-1) <|
     Hubcap.two 0 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_673_1, c6_673_2, c6_673_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_674_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_671l) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_674_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_671l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_674_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_671l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_674 :
    hubcapFit theRedpart rf6 p6_671l
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_674_1, c6_674_2, c6_674_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_679_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_678r) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_679_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_678r) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_679_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_678r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_679 :
    hubcapFit theRedpart rf6 p6_678r
    (Hubcap.two 1 2 0 <|
     Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_679_1, c6_679_2, c6_679_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_680_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_678l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_680_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_678l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_680_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_678l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_680 :
    hubcapFit theRedpart rf6 p6_678l
    (Hubcap.two 1 2 (-1) <|
     Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_680_1, c6_680_2, c6_680_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_685_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_684r) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_685_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_684r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_685_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_684r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_685 :
    hubcapFit theRedpart rf6 p6_684r
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_685_1, c6_685_2, c6_685_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_686_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_684l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_686_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_684l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_686_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_684l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_686 :
    hubcapFit theRedpart rf6 p6_684l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_686_1, c6_686_2, c6_686_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_689_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_688r) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_689_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_688r) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_689_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_688r) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_689 :
    hubcapFit theRedpart rf6 p6_688r
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_689_1, c6_689_2, c6_689_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_690_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_688l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_690_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_688l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_690_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_688l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_690 :
    hubcapFit theRedpart rf6 p6_688l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_690_1, c6_690_2, c6_690_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_693_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_692r) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_693_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_692r) (hubSubn 6 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_693_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_692r) (hubSubn 6 5 3) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_693 :
    hubcapFit theRedpart rf6 p6_692r
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 5 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_693_1, c6_693_2, c6_693_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_694_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_692l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_694_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_692l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_694_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_692l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_694 :
    hubcapFit theRedpart rf6 p6_692l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_694_1, c6_694_2, c6_694_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_699_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_698r) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_699_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_698r) (hubSubn 6 4 2) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_699_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_698r) (hubSubn 6 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_699 :
    hubcapFit theRedpart rf6 p6_698r
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 (-3) <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_699_1, c6_699_2, c6_699_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_700_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_698l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_700_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_698l) (hubSubn 6 4 2) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_700_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_698l) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_700 :
    hubcapFit theRedpart rf6 p6_698l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 (-2) <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_700_1, c6_700_2, c6_700_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_703_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_702r) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_703_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_702r) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_703_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_702r) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_703 :
    hubcapFit theRedpart rf6 p6_702r
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_703_1, c6_703_2, c6_703_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_704_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_702l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_704_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_702l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_704_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_702l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_704 :
    hubcapFit theRedpart rf6 p6_702l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_704_1, c6_704_2, c6_704_3]

end FourColor
