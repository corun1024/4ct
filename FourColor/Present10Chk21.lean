import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 21 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_955_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_954l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_955_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_954l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_955_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_954l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_955_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_954l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_955_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_954l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_955_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_954l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_955_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_954l) (hubSubn 10 5 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_955_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_954l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_955 :
    hubcapFit theRedpart rf10 p10_954l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_955_1, c10_955_2, c10_955_3, c10_955_4, c10_955_5, c10_955_6, c10_955_7, c10_955_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_959_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_959_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_959_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_959_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_959_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_959_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_959_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_958l) (hubSubn 10 5 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_959_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_958l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_959 :
    hubcapFit theRedpart rf10 p10_958l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_959_1, c10_959_2, c10_959_3, c10_959_4, c10_959_5, c10_959_6, c10_959_7, c10_959_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_961_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_958r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_961_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_958r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_961_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_958r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_961_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_958r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_961_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_958r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_961_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_958r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_961_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_958r) (hubSubn 10 5 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_961_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_958r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_961 :
    hubcapFit theRedpart rf10 p10_958r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_961_1, c10_961_2, c10_961_3, c10_961_4, c10_961_5, c10_961_6, c10_961_7, c10_961_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_964_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_957r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_964_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_957r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_964_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_957r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_964_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_957r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_964_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_957r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_964_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_957r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_964_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_957r) (hubSubn 10 5 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_964_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_957r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_964 :
    hubcapFit theRedpart rf10 p10_957r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_964_1, c10_964_2, c10_964_3, c10_964_4, c10_964_5, c10_964_6, c10_964_7, c10_964_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_981_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_980r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_981_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_980r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_981_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_980r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_981_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_980r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_981_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_980r) (hubSubn 10 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_981_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_980r) (hubSubn 10 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_981_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_980r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_981 :
    hubcapFit theRedpart rf10 p10_980r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_981_1, c10_981_2, c10_981_3, c10_981_4, c10_981_5, c10_981_6, c10_981_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_982_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_980l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_982_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_980l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_982_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_980l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_982_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_980l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_982_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_980l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_982_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_980l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_982_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_980l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_982_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_980l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_982_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_980l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_982 :
    hubcapFit theRedpart rf10 p10_980l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_982_1, c10_982_2, c10_982_3, c10_982_4, c10_982_5, c10_982_6, c10_982_7, c10_982_8, c10_982_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_984_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_978l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_984_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_978l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_984_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_978l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_984_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_978l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_984_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_978l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_984_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_978l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_984_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_978l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_984_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_978l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_984_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_978l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_984 :
    hubcapFit theRedpart rf10 p10_978l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_984_1, c10_984_2, c10_984_3, c10_984_4, c10_984_5, c10_984_6, c10_984_7, c10_984_8, c10_984_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_986_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_975l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_986_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_975l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_986_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_975l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_986_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_975l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_986_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_975l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_986_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_975l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_986_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_975l) (hubSubn 10 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_986_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_975l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_986 :
    hubcapFit theRedpart rf10 p10_975l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_986_1, c10_986_2, c10_986_3, c10_986_4, c10_986_5, c10_986_6, c10_986_7, c10_986_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_988_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_974l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_988_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_974l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_988_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_974l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_988_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_974l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_988_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_974l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_988_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_974l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_988_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_974l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_988_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_974l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_988_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_974l) (hubSubn 10 9 8) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_988 :
    hubcapFit theRedpart rf10 p10_974l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_988_1, c10_988_2, c10_988_3, c10_988_4, c10_988_5, c10_988_6, c10_988_7, c10_988_8, c10_988_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_990_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_973l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_990_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_973l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_990_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_973l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_990_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_973l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_990_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_973l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_990_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_973l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_990_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_973l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_990_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_973l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_990_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_973l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_990 :
    hubcapFit theRedpart rf10 p10_973l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_990_1, c10_990_2, c10_990_3, c10_990_4, c10_990_5, c10_990_6, c10_990_7, c10_990_8, c10_990_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_972l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_972l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_972l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_972l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_972l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_972l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_972l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_972l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_972l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_992_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_972l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_992 :
    hubcapFit theRedpart rf10 p10_972l
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
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_992_1, c10_992_2, c10_992_3, c10_992_4, c10_992_5, c10_992_6, c10_992_7, c10_992_8, c10_992_9, c10_992_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_971l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_971l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_994_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_994 :
    hubcapFit theRedpart rf10 p10_971l
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
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_994_1, c10_994_2, c10_994_3, c10_994_4, c10_994_5, c10_994_6, c10_994_7, c10_994_8, c10_994_9, c10_994_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_996_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_996_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_970l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_996_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_996_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_996_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_970l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_996_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_970l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_996_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_996_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_996_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_970l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_996 :
    hubcapFit theRedpart rf10 p10_970l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_996_1, c10_996_2, c10_996_3, c10_996_4, c10_996_5, c10_996_6, c10_996_7, c10_996_8, c10_996_9]

end FourColor
