import FourColor.Present10Step2
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 3 of the arity 10 presentation

A chunk of the case analysis of `present10.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step862 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842)
    (L3_4 : Successful q10_853) :
    SucceedsIn q10_414 p10_854r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step861 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step881 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_853 p10_877r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 9 3 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_880
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_879

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step883 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_877 p10_877l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_882

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step885 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_876 p10_876l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.two 7 9 7 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_884

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step887 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_875 p10_875l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_886

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step888 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_853 p10_873r := by
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact s10_step887 hred L3_1 L3_2 L3_3
  intro _
  refine succeed_by_split .hat 8 5 true (by decide +kernel) ?_ ?_
  · exact s10_step885 hred L3_1 L3_2 L3_3
  intro _
  refine succeed_by_split .hat 9 5 false (by decide +kernel) ?_ ?_
  · exact s10_step883 hred L3_1 L3_2 L3_3
  intro _
  exact s10_step881 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step890 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_873 p10_873l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_889

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step892 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_853 p10_870r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_891
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact s10_step890 hred L3_1 L3_2 L3_3
  intro _
  exact s10_step888 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step894 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_853 p10_869r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_893
  intro _
  exact s10_step892 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step896 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_853 p10_867r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_895
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step894 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step898 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_853 p10_864r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_897
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step896 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step900 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_853 p10_863r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 9 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_899
  intro _
  exact s10_step898 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step902 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_853 p10_853l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_901
  intro _
  exact s10_step900 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step904 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_414 p10_851r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_903
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact s10_step902 hred L3_1 L3_2 L3_3
  intro L3_4
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step862 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step906 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_414 p10_850r := by
  refine succeed_by_split .fan1 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_905
  intro _
  exact s10_step904 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step908 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_850 p10_850l := by
  exact succeed_by_hubcap10 hred
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
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_907

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step910 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_849 p10_849l := by
  exact succeed_by_hubcap10 hred
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
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_909

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step912 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_414 p10_847r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_911
  intro _
  refine succeed_by_split .hat 8 6 false (by decide +kernel) ?_ ?_
  · exact s10_step910 hred L3_1 L3_2 L3_3
  intro _
  refine succeed_by_split .hat 9 6 false (by decide +kernel) ?_ ?_
  · exact s10_step908 hred L3_1 L3_2 L3_3
  intro _
  exact s10_step906 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step914 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_414 p10_846r := by
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_913
  intro _
  exact s10_step912 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step916 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_414 p10_845r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_915
  intro _
  exact s10_step914 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step918 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842) :
    SucceedsIn q10_845 p10_845l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_917

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step923 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840) :
    SucceedsIn q10_842 p10_920r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_922

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step925 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840) :
    SucceedsIn q10_842 p10_919r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_924
  intro _
  exact s10_step923 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step927 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840) :
    SucceedsIn q10_842 p10_842l := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 8 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_926
  intro _
  exact s10_step925 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step928 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840) :
    SucceedsIn q10_414 p10_841r := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact s10_step927 hred L3_1 L3_2
  intro L3_3
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s10_step918 hred L3_1 L3_2 L3_3
  intro _
  exact s10_step916 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step941 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_840 p10_937r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_940
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_939

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step943 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_937 p10_937l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_942

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step945 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_936 p10_936l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_944

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step947 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_935 p10_935l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_946

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step949 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_934 p10_934l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_948

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step950 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_840 p10_933r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s10_step949 hred L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact s10_step947 hred L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact s10_step945 hred L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact s10_step943 hred L3_1 L4_1
  intro _
  exact s10_step941 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step952 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_840 p10_931r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 8 <|
       Hubcap.two 1 6 8 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_951
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step950 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step983 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_930 p10_979r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_982
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_981

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step985 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_930 p10_977r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_984
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step983 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step987 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_930 p10_974r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 6 7 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_986
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step985 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step989 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_930 p10_973r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_988
  intro _
  exact s10_step987 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step991 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_930 p10_972r := by
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_990
  intro _
  exact s10_step989 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step993 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_972 p10_972l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_992

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step995 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_971 p10_971l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_994

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step997 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_930 p10_969r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_996
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s10_step995 hred L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact s10_step993 hred L3_1 L4_1
  intro _
  exact s10_step991 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step999 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_930 p10_968r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 4 6 7 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_998
  intro _
  exact s10_step997 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1002 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_968 p10_968l := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1001

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1003 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L4_1 : Successful q10_929) :
    SucceedsIn q10_840 p10_929r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
    · exact s10_step1002 hred L3_1 L4_1
    intro _
    exact s10_step999 hred L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 true L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact h10_967 hred _
  intro _
  exact s10_step952 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1009 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838) :
    SucceedsIn q10_929 p10_1005r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 8 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1008
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1007

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1011 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838) :
    SucceedsIn q10_929 p10_1004r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1010
  intro _
  exact s10_step1009 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1014 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838) :
    SucceedsIn q10_1004 p10_1004l := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1013

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1015 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838) :
    SucceedsIn q10_414 p10_839r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
      · exact s10_step1014 hred L3_1
      intro _
      exact s10_step1011 hred L3_1
    intro L4_1
    exact s10_step1003 hred L3_1 L4_1
  intro L3_2
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step928 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1043 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020)
    (L4_4 : Successful q10_1034) :
    SucceedsIn q10_838 p10_1040r := by
  refine succeed_by_split .fan1 8 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1042

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1044 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020)
    (L4_4 : Successful q10_1034) :
    SucceedsIn q10_838 p10_1036r := by
  refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step1043 hred L4_1 L4_2 L4_3 L4_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1051 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_1034 p10_1047r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1050
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1049

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1053 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_1034 p10_1045r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1052
  intro _
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step1051 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1055 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_1034 p10_1034l := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1054
  intro _
  exact s10_step1053 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1057 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_838 p10_1032r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 7 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1056
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step1055 hred L4_1 L4_2 L4_3
  intro L4_4
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step1044 hred L4_1 L4_2 L4_3 L4_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1059 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_838 p10_1030r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.two 8 9 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1058
  intro _
  refine succeed_by_split .fan1 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step1057 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1061 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_838 p10_1029r := by
  refine succeed_by_split .hat 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 9 3 <|
       Hubcap.two 7 8 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1060
  intro _
  exact s10_step1059 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1063 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_1029 p10_1029l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1062

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1065 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_838 p10_1027r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1064
  intro _
  refine succeed_by_split .hat 8 6 false (by decide +kernel) ?_ ?_
  · exact s10_step1063 hred L4_1 L4_2 L4_3
  intro _
  exact s10_step1061 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1067 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_838 p10_1025r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.two 6 7 5 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1066
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step1065 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1069 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_838 p10_1024r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.two 8 9 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1068
  intro _
  exact s10_step1067 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1071 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_838 p10_1023r := by
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1070
  intro _
  exact s10_step1069 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1073 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_838 p10_1022r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1072
  intro _
  exact s10_step1071 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1075 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018)
    (L4_3 : Successful q10_1020) :
    SucceedsIn q10_838 p10_1021r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.two 6 7 5 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1074
  intro _
  exact s10_step1073 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1077 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L4_2 : Successful q10_1018) :
    SucceedsIn q10_838 p10_1019r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 2 3 9 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1076
  intro L4_3
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step1075 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1083 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L5_1 : Successful q10_1078) :
    SucceedsIn q10_1018 p10_1079r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1082
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1081

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1086 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016)
    (L5_1 : Successful q10_1078) :
    SucceedsIn q10_1079 p10_1079l := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1085

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1091 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016) :
    SucceedsIn q10_1078 p10_1087r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1090
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1089

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1093 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016) :
    SucceedsIn q10_1087 p10_1087l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1092

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1094 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q10_1016) :
    SucceedsIn q10_838 p10_1017r := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
      · exact s10_step1093 hred L4_1
      intro _
      exact s10_step1091 hred L4_1
    intro L5_1
    refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
    · exact s10_step1086 hred L4_1 L5_1
    intro _
    exact s10_step1083 hred L4_1 L5_1
  intro L4_2
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step1077 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1102 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q10_1095)
    (L5_2 : Successful q10_1097) :
    SucceedsIn q10_1016 p10_1098r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1101
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1100

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1107 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q10_1095) :
    SucceedsIn q10_1097 p10_1103r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1106
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_1105

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1109 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q10_1095) :
    SucceedsIn q10_1097 p10_1097l := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1108
  intro _
  exact s10_step1107 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1111 (hred : RedpartSound theRedpart) :
    SucceedsIn q10_1016 p10_1016l := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_1110
  intro L5_1
  refine succeed_by_split .spoke 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact s10_step1109 hred L5_1
  intro L5_2
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step1102 hred L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1112 (hred : RedpartSound theRedpart) :
    SucceedsIn q10_414 p10_414l := by
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
    · exact s10_step1111 hred
    intro L4_1
    refine succeed_by_split .spoke 0 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 1 false L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s10_step1094 hred L4_1
  intro L3_1
  refine succeed_by_split .spoke 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step1015 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step1113 (hred : RedpartSound theRedpart) :
    SucceedsIn q10_14 p10_14l := by
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact s10_step1112 hred
  intro L2_1
  refine succeed_by_split .spoke 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact s10_step837 hred L2_1
  intro L2_2
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step622 hred L2_1 L2_2

end FourColor
