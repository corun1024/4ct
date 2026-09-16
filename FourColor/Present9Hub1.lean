import FourColor.Present9Chk1
import FourColor.Present9Chk2
import FourColor.Present9Chk3
import FourColor.Present9Chk4
import FourColor.Present9Chk5
import FourColor.Present9Chk6
import FourColor.Present9Chk7
import FourColor.Present9Chk8
import FourColor.Present9Chk9
import FourColor.Present9Chk10
import FourColor.Present9Chk11
import FourColor.Present9Chk12
import FourColor.Present9Chk13
import FourColor.Present9Chk14
import FourColor.Present9Chk15
import FourColor.Present9Chk16
import FourColor.Present9Chk17
import FourColor.Present9Chk18
import FourColor.Present9Chk19
import FourColor.Present9Chk20
import FourColor.Present9Chk21
import FourColor.Present9Chk22
import FourColor.Present9Chk23
import FourColor.Present9Chk24
import FourColor.Present9Chk25
import FourColor.Present9Chk26
import FourColor.Present9Chk27
import FourColor.Present9Chk28
import FourColor.Present9Chk29
import FourColor.Present9Chk30
import FourColor.Present9Chk31
import FourColor.Present9Chk32
import FourColor.Present9Chk33
import FourColor.Present9Chk34
import FourColor.Present9Chk35
import FourColor.Present9Chk36
import FourColor.Present9Chk37
import FourColor.Present9Chk38
import FourColor.Present9Chk39
import FourColor.Present9Chk40
import FourColor.Present9Chk41
import FourColor.Present9Chk42
import FourColor.Present9Chk43
import FourColor.Present9Chk44
import FourColor.Present9Chk45
import FourColor.Present9Chk46
import FourColor.Present9Chk47
import FourColor.Present9Chk48
import FourColor.Present9Chk49
import FourColor.Present9Chk50
import FourColor.Present9Chk51
import FourColor.Present9Chk52
import FourColor.Present9Chk53
import FourColor.Present9Chk54
import FourColor.Present9Chk55
import FourColor.Present9Chk56
import FourColor.Present9Chk57
import FourColor.Present9Chk58
import FourColor.Present9Chk59
import FourColor.Present9Chk60
import FourColor.Present9Chk61
import FourColor.Present9Chk62
import FourColor.Present9Chk63
import FourColor.Present9Chk64
import FourColor.Present9Chk65
import FourColor.Present9Chk66
import FourColor.Present9Chk67
import FourColor.Present9Chk68
import FourColor.Present9Chk69
import FourColor.Present9Chk70
import FourColor.Present9Chk71
import FourColor.Present9Chk72
import FourColor.Present9Chk73
import FourColor.Present9Chk74
import FourColor.Present9Chk75
import FourColor.Present9Chk76
import FourColor.Present9Chk77

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 1 of the arity 9 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_175 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_173l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 8 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_174

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_177 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_173r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 8 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_176

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_178 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_158l := by
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact h9_175 hred _
  intro _
  exact h9_177 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_181 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_179l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 8 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_180

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_183 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_179r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 8 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_182

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_184 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_157l := by
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact h9_181 hred _
  intro _
  exact h9_183 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_679 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_677l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 2 8 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_682 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_680l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 2 8 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_684 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_680r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 2 8 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_683

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_685 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_677r := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact h9_682 hred _
  intro _
  exact h9_684 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_686 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_342l := by
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact h9_679 hred _
  intro _
  exact h9_685 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_689 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_687l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_688

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_691 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_687r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_690

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_692 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_341l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h9_689 hred _
  intro _
  exact h9_691 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_697 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_695l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_696

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_699 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_695r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_698

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_700 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_339l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h9_697 hred _
  intro _
  exact h9_699 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_989 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_987l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_988

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_992 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_990l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_991

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_994 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_990r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_993

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_995 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_987r := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact h9_992 hred _
  intro _
  exact h9_994 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_996 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_927l := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact h9_989 hred _
  intro _
  exact h9_995 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1068 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1066l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1067

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1070 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1066r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1069

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1071 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1058l := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact h9_1068 hred _
  intro _
  exact h9_1070 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1082 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1080l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 7 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1081

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1084 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1080r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 7 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1083

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1085 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1075l := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact h9_1082 hred _
  intro _
  exact h9_1084 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1088 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1086l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1087

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1090 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1086r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1089

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1091 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1074l := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact h9_1088 hred _
  intro _
  exact h9_1090 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1126 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1124l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1125

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1128 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1124r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1127

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1129 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1015l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h9_1126 hred _
  intro _
  exact h9_1128 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1167 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1165l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1166

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1169 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1165r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1168

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1170 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1145l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact h9_1167 hred _
  intro _
  exact h9_1169 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1191 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1189l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1190

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1194 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1192l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1193

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1196 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1192r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1195

end FourColor
