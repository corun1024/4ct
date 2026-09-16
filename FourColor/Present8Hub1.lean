import FourColor.Present8Chk1
import FourColor.Present8Chk2
import FourColor.Present8Chk3
import FourColor.Present8Chk4
import FourColor.Present8Chk5
import FourColor.Present8Chk6
import FourColor.Present8Chk7
import FourColor.Present8Chk8
import FourColor.Present8Chk9
import FourColor.Present8Chk10
import FourColor.Present8Chk11
import FourColor.Present8Chk12
import FourColor.Present8Chk13
import FourColor.Present8Chk14
import FourColor.Present8Chk15
import FourColor.Present8Chk16
import FourColor.Present8Chk17
import FourColor.Present8Chk18
import FourColor.Present8Chk19
import FourColor.Present8Chk20
import FourColor.Present8Chk21
import FourColor.Present8Chk22
import FourColor.Present8Chk23
import FourColor.Present8Chk24
import FourColor.Present8Chk25
import FourColor.Present8Chk26
import FourColor.Present8Chk27
import FourColor.Present8Chk28
import FourColor.Present8Chk29
import FourColor.Present8Chk30
import FourColor.Present8Chk31
import FourColor.Present8Chk32
import FourColor.Present8Chk33
import FourColor.Present8Chk34
import FourColor.Present8Chk35
import FourColor.Present8Chk36
import FourColor.Present8Chk37
import FourColor.Present8Chk38
import FourColor.Present8Chk39
import FourColor.Present8Chk40
import FourColor.Present8Chk41
import FourColor.Present8Chk42
import FourColor.Present8Chk43
import FourColor.Present8Chk44
import FourColor.Present8Chk45
import FourColor.Present8Chk46
import FourColor.Present8Chk47
import FourColor.Present8Chk48
import FourColor.Present8Chk49
import FourColor.Present8Chk50
import FourColor.Present8Chk51
import FourColor.Present8Chk52
import FourColor.Present8Chk53
import FourColor.Present8Chk54
import FourColor.Present8Chk55
import FourColor.Present8Chk56
import FourColor.Present8Chk57
import FourColor.Present8Chk58
import FourColor.Present8Chk59
import FourColor.Present8Chk60
import FourColor.Present8Chk61
import FourColor.Present8Chk62
import FourColor.Present8Chk63
import FourColor.Present8Chk64
import FourColor.Present8Chk65
import FourColor.Present8Chk66
import FourColor.Present8Chk67
import FourColor.Present8Chk68
import FourColor.Present8Chk69
import FourColor.Present8Chk70
import FourColor.Present8Chk71
import FourColor.Present8Chk72
import FourColor.Present8Chk73
import FourColor.Present8Chk74
import FourColor.Present8Chk75
import FourColor.Present8Chk76
import FourColor.Present8Chk77
import FourColor.Present8Chk78
import FourColor.Present8Chk79
import FourColor.Present8Chk80
import FourColor.Present8Chk81
import FourColor.Present8Chk82
import FourColor.Present8Chk83
import FourColor.Present8Chk84
import FourColor.Present8Chk85
import FourColor.Present8Chk86
import FourColor.Present8Chk87
import FourColor.Present8Chk88
import FourColor.Present8Chk89
import FourColor.Present8Chk90
import FourColor.Present8Chk91
import FourColor.Present8Chk92
import FourColor.Present8Chk93
import FourColor.Present8Chk94
import FourColor.Present8Chk95
import FourColor.Present8Chk96
import FourColor.Present8Chk97
import FourColor.Present8Chk98
import FourColor.Present8Chk99
import FourColor.Present8Chk100
import FourColor.Present8Chk101
import FourColor.Present8Chk102
import FourColor.Present8Chk103
import FourColor.Present8Chk104
import FourColor.Present8Chk105
import FourColor.Present8Chk106
import FourColor.Present8Chk107
import FourColor.Present8Chk108
import FourColor.Present8Chk109
import FourColor.Present8Chk110

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 1 of the arity 8 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_804 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_802l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 6 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_803

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_806 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_802r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 6 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_805

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_807 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_797l := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact h8_804 hred _
  intro _
  exact h8_806 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1565 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1563l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1564

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1567 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1563r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1566

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1568 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1562l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1565 hred _
  intro _
  exact h8_1567 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1570 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1562r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1569

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1571 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1561r := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1568 hred _
  intro _
  exact h8_1570 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1575 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1573l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1574

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1577 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1573r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1576

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1578 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1572l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1575 hred _
  intro _
  exact h8_1577 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1580 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1572r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1579

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1581 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1561l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1578 hred _
  intro _
  exact h8_1580 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1620 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1618l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1619

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1622 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1618r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1621

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1623 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1617l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1620 hred _
  intro _
  exact h8_1622 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1625 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1617r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1624

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1626 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1604l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1623 hred _
  intro _
  exact h8_1625 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1631 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1629l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1630

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1633 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1629r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1632

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1634 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1628l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1631 hred _
  intro _
  exact h8_1633 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1636 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1628r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1635

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1637 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1587l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1634 hred _
  intro _
  exact h8_1636 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1641 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1639l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1640

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1643 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1639r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1642

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1644 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1638l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1641 hred _
  intro _
  exact h8_1643 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1646 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1638r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1645

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1647 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1586l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1644 hred _
  intro _
  exact h8_1646 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1665 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1663l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1664

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1667 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1663r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1666

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1668 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1653l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1665 hred _
  intro _
  exact h8_1667 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1673 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1671l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1672

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1675 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1671r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1674

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1676 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1650l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1673 hred _
  intro _
  exact h8_1675 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1680 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1678l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1679

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1682 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1678r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1683 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1677l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1680 hred _
  intro _
  exact h8_1682 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1685 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1677r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1684

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1686 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1649l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1683 hred _
  intro _
  exact h8_1685 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1690 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1688l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1689

end FourColor
