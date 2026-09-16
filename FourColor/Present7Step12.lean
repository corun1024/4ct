import FourColor.Present7Step11
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 12 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5692 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5626 p7_5678r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5691
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5690 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5695 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5626 p7_5676r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5694
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 (-2) <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5693
  intro _
  exact s7_step5692 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5705 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5674 p7_5701r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5704
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5703

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5708 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5674 p7_5699r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.two 3 6 2 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5707
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5706
  intro _
  exact s7_step5705 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5711 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5674 p7_5697r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5710
  intro _
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5709
  intro _
  exact s7_step5708 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5714 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5674 p7_5674l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5713
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 (-2) <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5712
  intro _
  exact s7_step5711 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5716 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5626 p7_5672r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5715
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s7_step5714 hred L2_1
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5695 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5731 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L5_1 : Successful q7_5724) :
    SucceedsIn q7_5672 p7_5728r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5730

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5732 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L5_1 : Successful q7_5724) :
    SucceedsIn q7_5672 p7_5724r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5731 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5738 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5724 p7_5734r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 (-3) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5737
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-4) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5736

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5740 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5724 p7_5733r := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 (-3) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5739
  intro _
  exact s7_step5738 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5742 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5724 p7_5724l := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-4) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 (-3) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5741
  intro _
  exact s7_step5740 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5744 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5672 p7_5721r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-3) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5743
  intro _
  refine succeed_by_split .fan1 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact s7_step5742 hred L2_1
  intro L5_1
  exact s7_step5732 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5746 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5672 p7_5719r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 (-3) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5745
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5744 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5750 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5718 p7_5718l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5749
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5748

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5752 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5672 p7_5672l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5751
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5750 hred L2_1
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5746 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5754 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5626 p7_5670r := by
  refine succeed_by_split .spoke 4 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5753
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact s7_step5752 hred L2_1
  intro _
  exact s7_step5716 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5767 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5670 p7_5763r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-3) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5766
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-3) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5765

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5769 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5670 p7_5761r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 (-3) <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5768
  intro _
  exact s7_step5767 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5771 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5670 p7_5759r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 (-3) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5770
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5769 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5780 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5758 p7_5776r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 4 5 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5779
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5778

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5782 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5758 p7_5773r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5781
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5780 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5784 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5670 p7_5757r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 1 4 <|
         Hubcap.one 2 (-2) <|
         Hubcap.one 3 2 <|
         Hubcap.one 5 (-2) <|
         Hubcap.two 4 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5783
    intro _
    exact s7_step5782 hred L2_1
  intro _
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 (-3) <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5772
  intro _
  exact s7_step5771 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5786 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5670 p7_5756r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5785
  intro _
  exact s7_step5784 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5790 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5756 p7_5787r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5789

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5791 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5626 p7_5626l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
      · exact succeed_by_reducibility hred (by decide +kernel)
      intro _
      exact s7_step5790 hred L2_1
    intro _
    exact s7_step5786 hred L2_1
  intro _
  exact s7_step5754 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5792 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_877 p7_4977r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
    · exact s7_step5791 hred L2_1
    intro _
    exact s7_step5669 hred L2_1
  intro L2_2
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5624 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5811 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q7_5795)
    (L4_1 : Successful q7_5804)
    (L4_2 : Successful q7_5806) :
    SucceedsIn q7_5801 p7_5807r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 4 (-2) <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5810

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5815 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q7_5795)
    (L4_1 : Successful q7_5804) :
    SucceedsIn q7_5806 p7_5806l := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 (-2) <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 3 6 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 3 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5814
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 4 (-2) <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5813

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5820 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q7_5795) :
    SucceedsIn q7_5804 p7_5816r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 (-2) <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 3 6 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 3 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5819
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 4 (-2) <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5818

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5822 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q7_5795) :
    SucceedsIn q7_5801 p7_5803r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 4 (-2) <|
         Hubcap.one 5 (-2) <|
         Hubcap.two 0 2 7 <|
         Hubcap.two 1 3 6 <|
         Hubcap.two 1 6 6 <|
         Hubcap.two 3 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5821
    intro _
    exact s7_step5820 hred L3_1
  intro L4_1
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s7_step5815 hred L3_1 L4_1
  intro L4_2
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5811 hred L3_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5824 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q7_5795) :
    SucceedsIn q7_4976 p7_5800r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 4 (-4) <|
         Hubcap.one 5 0 <|
         Hubcap.two 0 2 7 <|
         Hubcap.two 1 3 6 <|
         Hubcap.two 1 6 6 <|
         Hubcap.two 3 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5823
    intro _
    exact s7_step5822 hred L3_1
  intro L3_2
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5825 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q7_5795) :
    SucceedsIn q7_4976 p7_5796r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5824 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5846 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5842r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5845
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5844

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5848 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5841r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5847
  intro _
  exact s7_step5846 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5853 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5840 p7_5849r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5852
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5851

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5855 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5840 p7_5840l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5854
  intro _
  exact s7_step5853 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5860 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5839 p7_5856r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5859
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5858

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5862 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5839 p7_5839l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5861
  intro _
  exact s7_step5860 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5868 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5838 p7_5864r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5867
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5866

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5870 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5838 p7_5863r := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5869
  intro _
  exact s7_step5868 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5875 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5863 p7_5871r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5874
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5873

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5877 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5863 p7_5863l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5876
  intro _
  exact s7_step5875 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5878 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5837r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact s7_step5877 hred
    intro _
    exact s7_step5870 hred
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s7_step5862 hred
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact s7_step5855 hred
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5848 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5880 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5836r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5879
  intro _
  exact s7_step5878 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5882 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5835r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-3) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5881
  intro _
  exact s7_step5880 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5890 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5834 p7_5886r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5889
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5888

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5892 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5834 p7_5884r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5891
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5890 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5894 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5834 p7_5883r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5893
  intro _
  exact s7_step5892 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5896 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5834 p7_5834l := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5895
  intro _
  exact s7_step5894 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5908 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5833 p7_5904r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5907
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5906

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5910 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5833 p7_5903r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5909
  intro _
  exact s7_step5908 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5912 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5833 p7_5902r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5911
  intro _
  exact s7_step5910 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5914 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5833 p7_5901r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-3) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5913
  intro _
  exact s7_step5912 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5916 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5833 p7_5900r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5915
  intro _
  exact s7_step5914 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5918 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5833 p7_5898r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5917
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5916 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5919 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5832r := by
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step5918 hred
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5896 hred
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5882 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5930 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5831 p7_5926r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5929
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5928

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5932 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5831 p7_5925r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 (-3) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5931
  intro _
  exact s7_step5930 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5934 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5831 p7_5924r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5933
  intro _
  exact s7_step5932 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5936 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5831 p7_5922r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5935
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5934 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5937 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5830r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step5936 hred
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5920
  intro _
  exact s7_step5919 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5941 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5828r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact succeed_by_hubcap7 hred
      (Hubcap.one 3 (-3) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5940
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5938
  intro _
  exact s7_step5937 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5948 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q7_5943)
    (L5_2 : Successful q7_5945) :
    SucceedsIn q7_5826 p7_5945r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-4) <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-4) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5947

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5959 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q7_5943) :
    SucceedsIn q7_5945 p7_5955r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-3) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5958
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5957

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5961 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q7_5943) :
    SucceedsIn q7_5945 p7_5952r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-3) <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5960
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5959 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5964 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q7_5943) :
    SucceedsIn q7_5945 p7_5950r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 (-3) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-3) <|
       Hubcap.two 0 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5963
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-3) <|
       Hubcap.two 0 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5962
  intro _
  exact s7_step5961 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5973 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q7_5943) :
    SucceedsIn q7_5950 p7_5969r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 6 (-2) <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5972
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5971

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5975 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q7_5943) :
    SucceedsIn q7_5950 p7_5968r := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 5 0 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 0 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 3 4 0 <|
       Hubcap.two 4 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5974
  intro _
  exact s7_step5973 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5978 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q7_5943) :
    SucceedsIn q7_5950 p7_5966r := by
  refine succeed_by_split .fan1 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 5 0 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 0 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 3 4 0 <|
       Hubcap.two 4 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5977
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 (-2) <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5976
  intro _
  exact s7_step5975 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5981 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q7_5943) :
    SucceedsIn q7_5950 p7_5950l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 0 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5980
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5979
  intro _
  exact s7_step5978 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5983 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q7_5943) :
    SucceedsIn q7_5945 p7_5945l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.two 0 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5982
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact s7_step5981 hred L5_1
  intro _
  exact s7_step5964 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5988 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5943 p7_5984r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5987
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5986

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5990 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5826 p7_5942r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 5 <|
         Hubcap.one 3 (-2) <|
         Hubcap.one 4 0 <|
         Hubcap.two 0 2 7 <|
         Hubcap.two 5 6 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5989
    intro _
    exact s7_step5988 hred
  intro L5_1
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact s7_step5983 hred L5_1
  intro L5_2
  exact s7_step5948 hred L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6003 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991)
    (L6_2 : Successful q7_5993) :
    SucceedsIn q7_5997 p7_5999r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 0 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_6002
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 3 4 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_6001

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6005 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991)
    (L6_2 : Successful q7_5993) :
    SucceedsIn q7_5942 p7_5996r := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 5 <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 1 <|
         Hubcap.two 0 6 2 <|
         Hubcap.two 2 3 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_6004
    intro _
    exact s7_step6003 hred L6_1 L6_2
  intro L6_3
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L6_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6008 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991)
    (L6_2 : Successful q7_5993) :
    SucceedsIn q7_5942 p7_5994r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_6007
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_6006
  intro _
  exact s7_step6005 hred L6_1 L6_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6016 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991)
    (L7_1 : Successful q7_6009)
    (L7_2 : Successful q7_6011) :
    SucceedsIn q7_5993 p7_6012r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L7_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_6015

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6021 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991)
    (L7_1 : Successful q7_6009) :
    SucceedsIn q7_6011 p7_6017r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 0 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_6020
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_6019

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6023 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991)
    (L7_1 : Successful q7_6009) :
    SucceedsIn q7_5993 p7_6010r := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 5 <|
         Hubcap.one 3 (-2) <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 1 <|
         Hubcap.one 6 (-1) <|
         Hubcap.two 0 2 7 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_6022
    intro _
    exact s7_step6021 hred L6_1 L7_1
  intro L7_2
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step6016 hred L6_1 L7_1 L7_2

end FourColor
