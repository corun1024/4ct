import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 55 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2801_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2800r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2801_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2800r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2801_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2800r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2801_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2800r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2801_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2800r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2801 :
    hubcapFit theRedpart rf8 p8_2800r
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2801_1, c8_2801_2, c8_2801_3, c8_2801_4, c8_2801_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2802_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2800l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2802_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2800l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2802_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2800l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2802_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2800l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2802_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2800l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2802 :
    hubcapFit theRedpart rf8 p8_2800l
    (Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2802_1, c8_2802_2, c8_2802_3, c8_2802_4, c8_2802_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2817_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2816r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2817_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2816r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2817_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2816r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2817_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2816r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2817_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2816r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2817_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2816r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2817_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2816r) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2817 :
    hubcapFit theRedpart rf8 p8_2816r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2817_1, c8_2817_2, c8_2817_3, c8_2817_4, c8_2817_5, c8_2817_6, c8_2817_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2818_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2816l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2818_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2816l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2818_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2816l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2818_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2816l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2818_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2816l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2818_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2816l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2818 :
    hubcapFit theRedpart rf8 p8_2816l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2818_1, c8_2818_2, c8_2818_3, c8_2818_4, c8_2818_5, c8_2818_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2820_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2815l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2820_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2820_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2815l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2820_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2820_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2815l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2820_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2815l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2820_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2815l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2820_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2815l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2820 :
    hubcapFit theRedpart rf8 p8_2815l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2820_1, c8_2820_2, c8_2820_3, c8_2820_4, c8_2820_5, c8_2820_6, c8_2820_7, c8_2820_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2822_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2813l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2822_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2813l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2822_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2813l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2822_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2813l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2822_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2813l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2822_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2813l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2822_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2813l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2822 :
    hubcapFit theRedpart rf8 p8_2813l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2822_1, c8_2822_2, c8_2822_3, c8_2822_4, c8_2822_5, c8_2822_6, c8_2822_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2824_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2812l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2824_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2812l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2824_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2812l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2824_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2812l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2824_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2812l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2824_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2812l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2824_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2812l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2824_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2812l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2824 :
    hubcapFit theRedpart rf8 p8_2812l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2824_1, c8_2824_2, c8_2824_3, c8_2824_4, c8_2824_5, c8_2824_6, c8_2824_7, c8_2824_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2826_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2810l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2826_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2810l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2826_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2810l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2826_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2810l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2826_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2810l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2826_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2810l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2826 :
    hubcapFit theRedpart rf8 p8_2810l
    (Hubcap.one 2 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2826_1, c8_2826_2, c8_2826_3, c8_2826_4, c8_2826_5, c8_2826_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2828_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2809l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2828_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2809l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2828_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2809l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2828_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2809l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2828_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2809l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2828_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2809l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2828_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2809l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2828 :
    hubcapFit theRedpart rf8 p8_2809l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2828_1, c8_2828_2, c8_2828_3, c8_2828_4, c8_2828_5, c8_2828_6, c8_2828_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2830_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2807l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2830_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2807l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2830_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2807l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2830_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2807l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2830_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2807l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2830 :
    hubcapFit theRedpart rf8 p8_2807l
    (Hubcap.one 2 1 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2830_1, c8_2830_2, c8_2830_3, c8_2830_4, c8_2830_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2832_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2806l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2832_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2806l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2832_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2806l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2832_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2806l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2832_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2806l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2832_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2806l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2832 :
    hubcapFit theRedpart rf8 p8_2806l
    (Hubcap.one 2 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2832_1, c8_2832_2, c8_2832_3, c8_2832_4, c8_2832_5, c8_2832_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2833_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2805l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2833_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2805l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2833_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2805l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2833_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2805l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2833_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2805l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2833 :
    hubcapFit theRedpart rf8 p8_2805l
    (Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2833_1, c8_2833_2, c8_2833_3, c8_2833_4, c8_2833_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2836_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2754l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2836_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2754l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2836_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2754l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2836_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2754l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2836 :
    hubcapFit theRedpart rf8 p8_2754l
    (Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2836_1, c8_2836_2, c8_2836_3, c8_2836_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2846_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2845r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2846_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2845r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2846_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2845r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2846_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2845r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2846_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2845r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2846 :
    hubcapFit theRedpart rf8 p8_2845r
    (Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2846_1, c8_2846_2, c8_2846_3, c8_2846_4, c8_2846_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2847_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2845l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2847_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2845l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2847_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2845l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2847_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2845l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2847_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2845l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2847 :
    hubcapFit theRedpart rf8 p8_2845l
    (Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2847_1, c8_2847_2, c8_2847_3, c8_2847_4, c8_2847_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2849_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2844l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2849_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2844l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2849_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2844l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2849_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2844l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2849_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2844l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2849 :
    hubcapFit theRedpart rf8 p8_2844l
    (Hubcap.one 3 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2849_1, c8_2849_2, c8_2849_3, c8_2849_4, c8_2849_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2854_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2853r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2854_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2853r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2854_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2853r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2854_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2853r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2854_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2853r) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2854_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2853r) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2854 :
    hubcapFit theRedpart rf8 p8_2853r
    (Hubcap.one 1 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2854_1, c8_2854_2, c8_2854_3, c8_2854_4, c8_2854_5, c8_2854_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2855_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2853l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2855_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2853l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2855_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2853l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2855_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2853l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2855_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2853l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2855_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2853l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2855 :
    hubcapFit theRedpart rf8 p8_2853l
    (Hubcap.one 2 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2855_1, c8_2855_2, c8_2855_3, c8_2855_4, c8_2855_5, c8_2855_6]

end FourColor
