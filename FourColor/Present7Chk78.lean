import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 78 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4184_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4183r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4184_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4183r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4184_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4183r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4184_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4183r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4184_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4183r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4184_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4183r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4184_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4183r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4184 :
    hubcapFit theRedpart rf7 p7_4183r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4184_1, c7_4184_2, c7_4184_3, c7_4184_4, c7_4184_5, c7_4184_6, c7_4184_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4185_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4185_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4185_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4183l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4185_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4183l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4185_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4183l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4185_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4183l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4185_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4183l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4185 :
    hubcapFit theRedpart rf7 p7_4183l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4185_1, c7_4185_2, c7_4185_3, c7_4185_4, c7_4185_5, c7_4185_6, c7_4185_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4187_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4187_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4187_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4182l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4187_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4182l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4187_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4182l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4187_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4182l) (hubSubn 7 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4187 :
    hubcapFit theRedpart rf7 p7_4182l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4187_1, c7_4187_2, c7_4187_3, c7_4187_4, c7_4187_5, c7_4187_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4189_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4189_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4189_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4189_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4180l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4189_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4180l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4189_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4180l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4189_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4180l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4189 :
    hubcapFit theRedpart rf7 p7_4180l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4189_1, c7_4189_2, c7_4189_3, c7_4189_4, c7_4189_5, c7_4189_6, c7_4189_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4191_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4179l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4191_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4179l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4191_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4179l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4191_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4179l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4191_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4179l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4191_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4179l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4191_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4179l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4191 :
    hubcapFit theRedpart rf7 p7_4179l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4191_1, c7_4191_2, c7_4191_3, c7_4191_4, c7_4191_5, c7_4191_6, c7_4191_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4193_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4178l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4193_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4178l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4193_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4178l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4193_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4178l) (hubSubn 7 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4193_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4178l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4193 :
    hubcapFit theRedpart rf7 p7_4178l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 3 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4193_1, c7_4193_2, c7_4193_3, c7_4193_4, c7_4193_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4194_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4177l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4194_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4177l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4194_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4177l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4194_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4177l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4194_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4177l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4194_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4177l) (hubSubn 7 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4194 :
    hubcapFit theRedpart rf7 p7_4177l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4194_1, c7_4194_2, c7_4194_3, c7_4194_4, c7_4194_5, c7_4194_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4196_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4196_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4176l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4196_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4176l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4196_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4176l) (hubSubn 7 5 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4196_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4176l) (hubSubn 7 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4196 :
    hubcapFit theRedpart rf7 p7_4176l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 2 <|
     Hubcap.two 2 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4196_1, c7_4196_2, c7_4196_3, c7_4196_4, c7_4196_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4197_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4197_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4175l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4197_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4175l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4197_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4175l) (hubSubn 7 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4197_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4175l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4197 :
    hubcapFit theRedpart rf7 p7_4175l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 3 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4197_1, c7_4197_2, c7_4197_3, c7_4197_4, c7_4197_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4209_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4208r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4209_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4208r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4209_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4208r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4209_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4208r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4209_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4208r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4209_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4208r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4209_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4208r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4209 :
    hubcapFit theRedpart rf7 p7_4208r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4209_1, c7_4209_2, c7_4209_3, c7_4209_4, c7_4209_5, c7_4209_6, c7_4209_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4210_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4208l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4210_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4208l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4210_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4208l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4210_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4208l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4210_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4208l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4210_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4208l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4210_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4208l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4210 :
    hubcapFit theRedpart rf7 p7_4208l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4210_1, c7_4210_2, c7_4210_3, c7_4210_4, c7_4210_5, c7_4210_6, c7_4210_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4212_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4212_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4212_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4207l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4212_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4207l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4212_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4207l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4212_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4207l) (hubSubn 7 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4212 :
    hubcapFit theRedpart rf7 p7_4207l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4212_1, c7_4212_2, c7_4212_3, c7_4212_4, c7_4212_5, c7_4212_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4213_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4213_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4213_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4213_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4213_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4206l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4213_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4206l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4213_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4213 :
    hubcapFit theRedpart rf7 p7_4206l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4213_1, c7_4213_2, c7_4213_3, c7_4213_4, c7_4213_5, c7_4213_6, c7_4213_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4215_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4205l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4215_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4205l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4215_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4205l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4215_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4205l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4215_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4205l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4215_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4205l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4215_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4205l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4215 :
    hubcapFit theRedpart rf7 p7_4205l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4215_1, c7_4215_2, c7_4215_3, c7_4215_4, c7_4215_5, c7_4215_6, c7_4215_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4217_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4203l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4217_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4203l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4217_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4203l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4217_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4203l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4217_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4203l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4217_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4203l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4217_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4203l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4217 :
    hubcapFit theRedpart rf7 p7_4203l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4217_1, c7_4217_2, c7_4217_3, c7_4217_4, c7_4217_5, c7_4217_6, c7_4217_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4219_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4202l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4219_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4202l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4219_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4202l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4219_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4202l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4219_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4202l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4219_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4202l) (hubSubn 7 5 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4219 :
    hubcapFit theRedpart rf7 p7_4202l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4219_1, c7_4219_2, c7_4219_3, c7_4219_4, c7_4219_5, c7_4219_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4220_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4201l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4220_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4201l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4220_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4201l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4220_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4201l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4220_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4201l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4220_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4201l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4220 :
    hubcapFit theRedpart rf7 p7_4201l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4220_1, c7_4220_2, c7_4220_3, c7_4220_4, c7_4220_5, c7_4220_6]

end FourColor
