import FourColor.Present7Step7
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 8 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3838 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3818r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3837
  intro _
  exact s7_step3836 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3841 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3816r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3840
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3839
  intro _
  exact s7_step3838 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3844 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3814r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3843
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3842
  intro _
  exact s7_step3841 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3847 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3812r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3846
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3845
  intro _
  exact s7_step3844 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3849 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3810r := by
  refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3848
  intro _
  exact s7_step3847 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3865 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3810 p7_3861r := by
  refine succeed_by_split .fan1 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3864
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3863

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3867 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3810 p7_3860r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3866
  intro _
  exact s7_step3865 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3870 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3810 p7_3858r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3869
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3868
  intro _
  exact s7_step3867 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3872 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3810 p7_3856r := by
  refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3871
  intro _
  exact s7_step3870 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3875 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3810 p7_3854r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3874
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3873
  intro _
  exact s7_step3872 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3878 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3810 p7_3852r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3877
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3876
  intro _
  exact s7_step3875 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3881 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3810 p7_3850r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3880
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3879
  intro _
  exact s7_step3878 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3883 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3809r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 5 0 <|
         Hubcap.two 4 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3882
    intro _
    exact s7_step3881 hred L1_1 L2_1
  intro _
  exact s7_step3849 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3886 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3807r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3885
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3884
  intro _
  exact s7_step3883 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3903 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3807 p7_3899r := by
  refine succeed_by_split .fan2 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3902
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3901

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3905 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3807 p7_3898r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3904
  intro _
  exact s7_step3903 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3907 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3807 p7_3895r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3906
  intro _
  refine succeed_by_split .fan2 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3905 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3909 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3807 p7_3893r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3908
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3907 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3912 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3807 p7_3891r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3911
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3910
  intro _
  exact s7_step3909 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3914 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3807 p7_3890r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3913
  intro _
  exact s7_step3912 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3916 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3807 p7_3888r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3915
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3914 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3918 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3807 p7_3887r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3917
  intro _
  exact s7_step3916 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3920 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3806r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 4 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 5 0 <|
         Hubcap.two 4 6 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3919
    intro _
    exact s7_step3918 hred L1_1 L2_1
  intro _
  exact s7_step3886 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3937 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3806 p7_3933r := by
  refine succeed_by_split .fan1 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3936
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3935

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3940 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3806 p7_3931r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3939
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3938
  intro _
  exact s7_step3937 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3943 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3806 p7_3929r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3942
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3941
  intro _
  exact s7_step3940 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3946 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3806 p7_3927r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3945
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3944
  intro _
  exact s7_step3943 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3949 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3806 p7_3925r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 4 3 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3948
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3947
  intro _
  exact s7_step3946 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3952 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3806 p7_3923r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3951
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3950
  intro _
  exact s7_step3949 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3955 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3806 p7_3921r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3954
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3953
  intro _
  exact s7_step3952 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3957 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3805r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 5 0 <|
         Hubcap.two 4 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3956
    intro _
    exact s7_step3955 hred L1_1 L2_1
  intro _
  exact s7_step3920 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3968 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3805 p7_3964r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3967
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3966

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3974 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3962 p7_3970r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3973
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3972

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3976 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3962 p7_3962l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3975
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3974 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3984 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3961 p7_3980r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3983
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3982

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3986 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3961 p7_3977r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3985
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3984 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3988 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3805 p7_3960r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 5 0 <|
         Hubcap.one 6 0 <|
         Hubcap.two 3 4 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3987
    intro _
    exact s7_step3986 hred L1_1 L2_1
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s7_step3976 hred L1_1 L2_1
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3968 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3991 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3805 p7_3958r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3990
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3989
  intro _
  exact s7_step3988 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3993 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3804r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 2 <|
         Hubcap.one 5 0 <|
         Hubcap.two 1 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3992
    intro _
    exact s7_step3991 hred L1_1 L2_1
  intro _
  exact s7_step3957 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3995 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3757l := by
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3994
  intro _
  exact s7_step3993 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4014 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3756 p7_4010r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4013
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4012

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4017 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3756 p7_4008r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4016
  intro _
  refine succeed_by_split .spoke 1 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4015
  intro _
  exact s7_step4014 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4024 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4007 p7_4020r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4023
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4022

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4027 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4007 p7_4018r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4026
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4025
  intro _
  exact s7_step4024 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4029 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3756 p7_4006r := by
  refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 2 <|
         Hubcap.one 4 0 <|
         Hubcap.one 6 1 <|
         Hubcap.two 1 5 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_4028
    intro _
    exact s7_step4027 hred L1_1 L2_1
  intro _
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4017 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4032 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3756 p7_4004r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4031
  intro _
  refine succeed_by_split .fan2 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4030
  intro _
  exact s7_step4029 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4042 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4003 p7_4038r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4041
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4040

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4045 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4003 p7_4036r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4044
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4043
  intro _
  exact s7_step4042 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4048 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4003 p7_4034r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4047
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4046
  intro _
  exact s7_step4045 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4049 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3756 p7_4002r := by
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4048 hred L1_1 L2_1
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4033
  intro _
  exact s7_step4032 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4052 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3756 p7_4000r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4051
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4050
  intro _
  exact s7_step4049 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4055 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3756 p7_3998r := by
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4054
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4053
  intro _
  exact s7_step4052 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4057 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3756 p7_3997r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 5 1 <|
       Hubcap.two 1 6 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4056
  intro _
  exact s7_step4055 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4072 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3997 p7_4068r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4071
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4070

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4075 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3997 p7_4066r := by
  refine succeed_by_split .spoke 1 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4074
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4073
  intro _
  exact s7_step4072 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4078 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3997 p7_4064r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4077
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4076
  intro _
  exact s7_step4075 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4080 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3997 p7_4062r := by
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4079
  intro _
  exact s7_step4078 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4089 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4062 p7_4085r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4088
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4087

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4091 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4062 p7_4083r := by
  refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4090
  intro _
  exact s7_step4089 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4094 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4062 p7_4081r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4093
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4092
  intro _
  exact s7_step4091 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4096 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3997 p7_4061r := by
  refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 2 <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 0 <|
         Hubcap.two 1 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_4095
    intro _
    exact s7_step4094 hred L1_1 L2_1
  intro _
  exact s7_step4080 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4099 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3997 p7_4059r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4098
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4097
  intro _
  exact s7_step4096 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4102 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3997 p7_3997l := by
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4101
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4100
  intro _
  exact s7_step4099 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4104 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3756 p7_3756l := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4103
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step4102 hred L1_1 L2_1
  intro _
  exact s7_step4057 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4105 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3581 p7_3581l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s7_step4104 hred L1_1 L2_1
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step3995 hred L1_1 L2_1
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step3803 hred L1_1 L2_1
  intro _
  exact s7_step3784 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4106 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_879 p7_3440r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s7_step4105 hred L1_1 L2_1
    intro L3_1
    refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_reducibility hred (by decide +kernel)
      intro _
      exact s7_step3755 hred L1_1 L2_1 L3_1
    intro L3_2
    exact s7_step3702 hred L1_1 L2_1 L3_1 L3_2
  intro L2_2
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step3580 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4124 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4111 p7_4120r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4123
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-2) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4122

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4126 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4111 p7_4117r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.two 2 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4125
  intro _
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4124 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4130 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4115 p7_4115l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 (-2) <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4129
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-2) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4128

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4131 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4111 p7_4113r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4130 hred L1_1 L2_1 L3_1
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4126 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4144 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133)
    (L5_2 : Successful q7_4136)
    (L5_3 : Successful q7_4138)
    (L5_4 : Successful q7_4141) :
    SucceedsIn q7_4113 p7_4141r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4143

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4148 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133)
    (L5_2 : Successful q7_4136)
    (L5_3 : Successful q7_4138) :
    SucceedsIn q7_4141 p7_4141l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4147
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4146

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4150 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133)
    (L5_2 : Successful q7_4136)
    (L5_3 : Successful q7_4138) :
    SucceedsIn q7_4113 p7_4139r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 3 <|
       Hubcap.two 2 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4149
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s7_step4148 hred L1_1 L2_1 L3_1 L5_1 L5_2 L5_3
  intro L5_4
  exact s7_step4144 hred L1_1 L2_1 L3_1 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4157 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133)
    (L5_2 : Successful q7_4136) :
    SucceedsIn q7_4138 p7_4153r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4156
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4155

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4159 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133)
    (L5_2 : Successful q7_4136) :
    SucceedsIn q7_4138 p7_4152r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4158
  intro _
  exact s7_step4157 hred L1_1 L2_1 L3_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4161 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133)
    (L5_2 : Successful q7_4136) :
    SucceedsIn q7_4138 p7_4138l := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4160
  intro _
  exact s7_step4159 hred L1_1 L2_1 L3_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4168 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4136 p7_4164r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4167
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4166

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4170 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4136 p7_4163r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4169
  intro _
  exact s7_step4168 hred L1_1 L2_1 L3_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4173 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4136 p7_4136l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 3 <|
       Hubcap.two 2 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4172
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4171
  intro _
  exact s7_step4170 hred L1_1 L2_1 L3_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4174 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4113 p7_4135r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4173 hred L1_1 L2_1 L3_1 L5_1
  intro L5_2
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact s7_step4161 hred L1_1 L2_1 L3_1 L5_1 L5_2
  intro L5_3
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step4150 hred L1_1 L2_1 L3_1 L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4186 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4135 p7_4182r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4185
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4184

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4188 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4135 p7_4180r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4187
  intro _
  exact s7_step4186 hred L1_1 L2_1 L3_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4190 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4135 p7_4179r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4189
  intro _
  exact s7_step4188 hred L1_1 L2_1 L3_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4192 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4135 p7_4178r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4191
  intro _
  exact s7_step4190 hred L1_1 L2_1 L3_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4195 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4135 p7_4176r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4194
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 3 <|
       Hubcap.two 2 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4193
  intro _
  exact s7_step4192 hred L1_1 L2_1 L3_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4198 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107)
    (L5_1 : Successful q7_4133) :
    SucceedsIn q7_4135 p7_4135l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 3 <|
       Hubcap.two 2 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4197
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 2 <|
       Hubcap.two 2 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4196
  intro _
  exact s7_step4195 hred L1_1 L2_1 L3_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4211 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4133 p7_4207r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4210
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4209

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4214 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4133 p7_4205r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4213
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4212
  intro _
  exact s7_step4211 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4216 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4133 p7_4204r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4215
  intro _
  exact s7_step4214 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4218 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4133 p7_4202r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4217
  intro _
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4216 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4221 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4133 p7_4200r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4220
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4219
  intro _
  exact s7_step4218 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4222 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4113 p7_4132r := by
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4221 hred L1_1 L2_1 L3_1
  intro L5_1
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact s7_step4198 hred L1_1 L2_1 L3_1 L5_1
  intro _
  exact s7_step4174 hred L1_1 L2_1 L3_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4224 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_4113 p7_4113l := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4223
  intro _
  exact s7_step4222 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4225 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_4107) :
    SucceedsIn q7_3440 p7_4109r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact s7_step4224 hred L1_1 L2_1 L3_1
    intro _
    exact s7_step4131 hred L1_1 L2_1 L3_1
  intro L3_2
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4239 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4107 p7_4235r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4238
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4237

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4241 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4107 p7_4234r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4240
  intro _
  exact s7_step4239 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4249 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4233 p7_4245r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4248
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4247

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4251 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4233 p7_4244r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4250
  intro _
  exact s7_step4249 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4253 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4233 p7_4243r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4252
  intro _
  exact s7_step4251 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4255 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4233 p7_4233l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4254
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4253 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4256 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4107 p7_4230r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4255 hred L1_1 L2_1 L4_1 L4_2
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4241 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4266 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4230 p7_4262r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4265
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4264

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4268 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4230 p7_4261r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4267
  intro _
  exact s7_step4266 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4270 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4230 p7_4260r := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4269
  intro _
  exact s7_step4268 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4280 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228)
    (L6_1 : Successful q7_4275) :
    SucceedsIn q7_4258 p7_4276r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4279

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4288 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4275 p7_4284r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4287
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4286

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4290 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4275 p7_4283r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4289
  intro _
  exact s7_step4288 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4292 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4275 p7_4282r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4291
  intro _
  exact s7_step4290 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4294 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4275 p7_4275l := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4293
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4292 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4295 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4258 p7_4272r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4294 hred L1_1 L2_1 L4_1 L4_2
  intro L6_1
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L6_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step4280 hred L1_1 L2_1 L4_1 L4_2 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4297 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4258 p7_4258l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4296
  intro _
  exact s7_step4295 hred L1_1 L2_1 L4_1 L4_2

end FourColor
