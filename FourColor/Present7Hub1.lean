import FourColor.Present7Chk1
import FourColor.Present7Chk2
import FourColor.Present7Chk3
import FourColor.Present7Chk4
import FourColor.Present7Chk5
import FourColor.Present7Chk6
import FourColor.Present7Chk7
import FourColor.Present7Chk8
import FourColor.Present7Chk9
import FourColor.Present7Chk10
import FourColor.Present7Chk11
import FourColor.Present7Chk12
import FourColor.Present7Chk13
import FourColor.Present7Chk14
import FourColor.Present7Chk15
import FourColor.Present7Chk16
import FourColor.Present7Chk17
import FourColor.Present7Chk18
import FourColor.Present7Chk19
import FourColor.Present7Chk20
import FourColor.Present7Chk21
import FourColor.Present7Chk22
import FourColor.Present7Chk23
import FourColor.Present7Chk24
import FourColor.Present7Chk25
import FourColor.Present7Chk26
import FourColor.Present7Chk27
import FourColor.Present7Chk28
import FourColor.Present7Chk29
import FourColor.Present7Chk30
import FourColor.Present7Chk31
import FourColor.Present7Chk32
import FourColor.Present7Chk33
import FourColor.Present7Chk34
import FourColor.Present7Chk35
import FourColor.Present7Chk36
import FourColor.Present7Chk37
import FourColor.Present7Chk38
import FourColor.Present7Chk39
import FourColor.Present7Chk40
import FourColor.Present7Chk41
import FourColor.Present7Chk42
import FourColor.Present7Chk43
import FourColor.Present7Chk44
import FourColor.Present7Chk45
import FourColor.Present7Chk46
import FourColor.Present7Chk47
import FourColor.Present7Chk48
import FourColor.Present7Chk49
import FourColor.Present7Chk50
import FourColor.Present7Chk51
import FourColor.Present7Chk52
import FourColor.Present7Chk53
import FourColor.Present7Chk54
import FourColor.Present7Chk55
import FourColor.Present7Chk56
import FourColor.Present7Chk57
import FourColor.Present7Chk58
import FourColor.Present7Chk59
import FourColor.Present7Chk60
import FourColor.Present7Chk61
import FourColor.Present7Chk62
import FourColor.Present7Chk63
import FourColor.Present7Chk64
import FourColor.Present7Chk65
import FourColor.Present7Chk66
import FourColor.Present7Chk67
import FourColor.Present7Chk68
import FourColor.Present7Chk69
import FourColor.Present7Chk70
import FourColor.Present7Chk71
import FourColor.Present7Chk72
import FourColor.Present7Chk73
import FourColor.Present7Chk74
import FourColor.Present7Chk75
import FourColor.Present7Chk76
import FourColor.Present7Chk77
import FourColor.Present7Chk78
import FourColor.Present7Chk79
import FourColor.Present7Chk80
import FourColor.Present7Chk81
import FourColor.Present7Chk82
import FourColor.Present7Chk83
import FourColor.Present7Chk84
import FourColor.Present7Chk85
import FourColor.Present7Chk86
import FourColor.Present7Chk87
import FourColor.Present7Chk88
import FourColor.Present7Chk89
import FourColor.Present7Chk90
import FourColor.Present7Chk91
import FourColor.Present7Chk92
import FourColor.Present7Chk93
import FourColor.Present7Chk94
import FourColor.Present7Chk95
import FourColor.Present7Chk96
import FourColor.Present7Chk97
import FourColor.Present7Chk98
import FourColor.Present7Chk99
import FourColor.Present7Chk100
import FourColor.Present7Chk101
import FourColor.Present7Chk102
import FourColor.Present7Chk103
import FourColor.Present7Chk104
import FourColor.Present7Chk105
import FourColor.Present7Chk106
import FourColor.Present7Chk107
import FourColor.Present7Chk108
import FourColor.Present7Chk109
import FourColor.Present7Chk110
import FourColor.Present7Chk111
import FourColor.Present7Chk112
import FourColor.Present7Chk113

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 1 of the arity 7 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h7_3698 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p7_3696l := by
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3697

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h7_3700 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p7_3696r := by
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3699

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h7_3701 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p7_3583l := by
  refine succeed_by_split .spoke 1 7 true (by decide +kernel) ?_ ?_
  · exact h7_3698 hred _
  intro _
  exact h7_3700 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h7_4565 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p7_4563l := by
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4564

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h7_4567 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p7_4563r := by
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4566

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h7_4568 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p7_4544l := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h7_4565 hred _
  intro _
  exact h7_4567 hred _

end FourColor
