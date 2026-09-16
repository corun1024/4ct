import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 19 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_961_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_960r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_961_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_960r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_961_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_960r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_961_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_960r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_961_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_960r) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_961_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_960r) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_961 :
    hubcapFit theRedpart rf8 p8_960r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_961_1, c8_961_2, c8_961_3, c8_961_4, c8_961_5, c8_961_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_962_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_960l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_962_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_960l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_962_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_960l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_962_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_960l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_962_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_960l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_962_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_960l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_962 :
    hubcapFit theRedpart rf8 p8_960l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_962_1, c8_962_2, c8_962_3, c8_962_4, c8_962_5, c8_962_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_964_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_964_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_959l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_964_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_959l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_964_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_964_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_959l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_964_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_959l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_964 :
    hubcapFit theRedpart rf8 p8_959l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_964_1, c8_964_2, c8_964_3, c8_964_4, c8_964_5, c8_964_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_965_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_965_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_958l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_965_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_965_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_958l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_965_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_965_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_965_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_958l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_965 :
    hubcapFit theRedpart rf8 p8_958l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 3 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_965_1, c8_965_2, c8_965_3, c8_965_4, c8_965_5, c8_965_6, c8_965_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_967_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_967_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_957l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_967_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_957l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_967_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_957l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_967_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_967_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_967_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_957l) (hubSubn 8 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_967 :
    hubcapFit theRedpart rf8 p8_957l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_967_1, c8_967_2, c8_967_3, c8_967_4, c8_967_5, c8_967_6, c8_967_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_969_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_956l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_969_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_956l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_969_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_956l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_969_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_956l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_969_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_956l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_969_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_956l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_969_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_956l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_969 :
    hubcapFit theRedpart rf8 p8_956l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_969_1, c8_969_2, c8_969_3, c8_969_4, c8_969_5, c8_969_6, c8_969_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_971_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_954l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_971_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_954l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_971_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_954l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_971_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_954l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_971_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_954l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_971_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_954l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_971 :
    hubcapFit theRedpart rf8 p8_954l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_971_1, c8_971_2, c8_971_3, c8_971_4, c8_971_5, c8_971_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_973_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_953l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_973_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_953l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_973_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_953l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_973_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_953l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_973_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_953l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_973_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_953l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_973 :
    hubcapFit theRedpart rf8 p8_953l
    (Hubcap.one 1 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_973_1, c8_973_2, c8_973_3, c8_973_4, c8_973_5, c8_973_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_975_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_885l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_975_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_885l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_975_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_885l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_975_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_885l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_975_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_885l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_975 :
    hubcapFit theRedpart rf8 p8_885l
    (Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_975_1, c8_975_2, c8_975_3, c8_975_4, c8_975_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_976_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_884l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_976_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_884l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_976_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_884l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_976_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_884l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_976_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_884l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_976_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_884l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_976 :
    hubcapFit theRedpart rf8 p8_884l
    (Hubcap.one 6 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_976_1, c8_976_2, c8_976_3, c8_976_4, c8_976_5, c8_976_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_988_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_987r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_988_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_987r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_988_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_987r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_988_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_987r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_988_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_987r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_988_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_987r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_988_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_987r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_988 :
    hubcapFit theRedpart rf8 p8_987r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_988_1, c8_988_2, c8_988_3, c8_988_4, c8_988_5, c8_988_6, c8_988_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_989_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_987l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_989_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_987l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_989_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_987l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_989_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_987l) (hubSubn 8 4 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_989_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_987l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_989_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_987l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_989_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_987l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_989 :
    hubcapFit theRedpart rf8 p8_987l
    (Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_989_1, c8_989_2, c8_989_3, c8_989_4, c8_989_5, c8_989_6, c8_989_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_991_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_986l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_991_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_986l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_991_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_986l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_991_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_986l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_991_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_986l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_991_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_986l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_991_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_986l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_991 :
    hubcapFit theRedpart rf8 p8_986l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_991_1, c8_991_2, c8_991_3, c8_991_4, c8_991_5, c8_991_6, c8_991_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_993_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_985l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_993_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_985l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_993_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_985l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_993_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_985l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_993_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_985l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_993_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_985l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_993_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_985l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_993 :
    hubcapFit theRedpart rf8 p8_985l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_993_1, c8_993_2, c8_993_3, c8_993_4, c8_993_5, c8_993_6, c8_993_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_995_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_984l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_995_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_984l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_995_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_984l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_995_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_984l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_995_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_984l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_995_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_984l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_995 :
    hubcapFit theRedpart rf8 p8_984l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_995_1, c8_995_2, c8_995_3, c8_995_4, c8_995_5, c8_995_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_996_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_983l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_996_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_983l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_996_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_983l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_996_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_983l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_996_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_983l) (hubSubn 8 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_996_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_983l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_996 :
    hubcapFit theRedpart rf8 p8_983l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_996_1, c8_996_2, c8_996_3, c8_996_4, c8_996_5, c8_996_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_998_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_982l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_998_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_982l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_998_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_982l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_998_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_982l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_998_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_982l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_998_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_982l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_998 :
    hubcapFit theRedpart rf8 p8_982l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_998_1, c8_998_2, c8_998_3, c8_998_4, c8_998_5, c8_998_6]

end FourColor
