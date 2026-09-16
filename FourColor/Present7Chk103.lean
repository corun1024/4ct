import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 103 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5481_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5471l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5481_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5471l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5481_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5471l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5481_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5471l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5481_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5471l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5481_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5471l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5481 :
    hubcapFit theRedpart rf7 p7_5471l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5481_1, c7_5481_2, c7_5481_3, c7_5481_4, c7_5481_5, c7_5481_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5483_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5470l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5483_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5470l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5483_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5470l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5483_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5470l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5483_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5470l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5483_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5470l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5483_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5470l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5483 :
    hubcapFit theRedpart rf7 p7_5470l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5483_1, c7_5483_2, c7_5483_3, c7_5483_4, c7_5483_5, c7_5483_6, c7_5483_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5485_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5485_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5485_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5469l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5485_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5469l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5485_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5469l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5485_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5469l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5485 :
    hubcapFit theRedpart rf7 p7_5469l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5485_1, c7_5485_2, c7_5485_3, c7_5485_4, c7_5485_5, c7_5485_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5489_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5488r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5489_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5488r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5489_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5488r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5489_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5488r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5489_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5488r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5489_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5488r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5489_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5488r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5489 :
    hubcapFit theRedpart rf7 p7_5488r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5489_1, c7_5489_2, c7_5489_3, c7_5489_4, c7_5489_5, c7_5489_6, c7_5489_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5490_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5490_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5490_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5488l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5490_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5490_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5490_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5490_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5488l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5490 :
    hubcapFit theRedpart rf7 p7_5488l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5490_1, c7_5490_2, c7_5490_3, c7_5490_4, c7_5490_5, c7_5490_6, c7_5490_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5492_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5492_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5492_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5487l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5492_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5487l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5492_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5487l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5492_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5487l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5492 :
    hubcapFit theRedpart rf7 p7_5487l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5492_1, c7_5492_2, c7_5492_3, c7_5492_4, c7_5492_5, c7_5492_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5494_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5406l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5494_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5406l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5494_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5406l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5494_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5406l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5494_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5406l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5494 :
    hubcapFit theRedpart rf7 p7_5406l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5494_1, c7_5494_2, c7_5494_3, c7_5494_4, c7_5494_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5508_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5507r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5508_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5507r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5508_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5507r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5508_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5507r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5508_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5507r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5508_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5507r) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5508 :
    hubcapFit theRedpart rf7 p7_5507r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5508_1, c7_5508_2, c7_5508_3, c7_5508_4, c7_5508_5, c7_5508_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5509_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5507l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5509_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5507l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5509_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5507l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5509_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5507l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5509_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5507l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5509_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5507l) (hubSubn 7 5 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5509 :
    hubcapFit theRedpart rf7 p7_5507l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5509_1, c7_5509_2, c7_5509_3, c7_5509_4, c7_5509_5, c7_5509_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5511_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5506l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5511_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5506l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5511_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5506l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5511_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5506l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5511_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5506l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5511_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5506l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5511_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5506l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5511 :
    hubcapFit theRedpart rf7 p7_5506l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5511_1, c7_5511_2, c7_5511_3, c7_5511_4, c7_5511_5, c7_5511_6, c7_5511_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5513_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5513_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5513_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5505l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5513_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5505l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5513_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5505l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5513_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5505l) (hubSubn 7 5 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5513 :
    hubcapFit theRedpart rf7 p7_5505l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5513_1, c7_5513_2, c7_5513_3, c7_5513_4, c7_5513_5, c7_5513_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5514_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5504l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5514_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5504l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5514_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5504l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5514_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5504l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5514_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5504l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5514_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5504l) (hubSubn 7 5 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5514 :
    hubcapFit theRedpart rf7 p7_5504l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5514_1, c7_5514_2, c7_5514_3, c7_5514_4, c7_5514_5, c7_5514_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5516_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5503l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5516_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5503l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5516_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5503l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5516_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5503l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5516_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5503l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5516_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5503l) (hubSubn 7 5 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5516 :
    hubcapFit theRedpart rf7 p7_5503l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.two 2 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5516_1, c7_5516_2, c7_5516_3, c7_5516_4, c7_5516_5, c7_5516_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5517_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5502l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5517_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5502l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5517_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5502l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5517_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5502l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5517_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5502l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5517_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5502l) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5517 :
    hubcapFit theRedpart rf7 p7_5502l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5517_1, c7_5517_2, c7_5517_3, c7_5517_4, c7_5517_5, c7_5517_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5519_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5500l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5519_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5500l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5519_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5500l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5519_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5500l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5519_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5500l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5519_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5500l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5519 :
    hubcapFit theRedpart rf7 p7_5500l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5519_1, c7_5519_2, c7_5519_3, c7_5519_4, c7_5519_5, c7_5519_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5521_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5499l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5521_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5499l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5521_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5499l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5521_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5499l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5521_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5499l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5521_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5499l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5521 :
    hubcapFit theRedpart rf7 p7_5499l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5521_1, c7_5521_2, c7_5521_3, c7_5521_4, c7_5521_5, c7_5521_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5522_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5498l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5522_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5498l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5522_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5498l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5522_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5498l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5522_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5498l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5522_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5498l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5522 :
    hubcapFit theRedpart rf7 p7_5498l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5522_1, c7_5522_2, c7_5522_3, c7_5522_4, c7_5522_5, c7_5522_6]

end FourColor
