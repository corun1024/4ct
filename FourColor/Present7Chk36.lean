import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 36 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1976_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1974l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1976_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1974l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1976_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1974l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1976_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1974l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1976 :
    hubcapFit theRedpart rf7 p7_1974l
    (Hubcap.one 0 3 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1976_1, c7_1976_2, c7_1976_3, c7_1976_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1981_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1980r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1981_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1980r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1981_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1980r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1981_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1980r) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1981_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1980r) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1981 :
    hubcapFit theRedpart rf7 p7_1980r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1981_1, c7_1981_2, c7_1981_3, c7_1981_4, c7_1981_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1982_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1980l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1982_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1980l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1982_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1980l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1982_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1980l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1982_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1980l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1982_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1980l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1982 :
    hubcapFit theRedpart rf7 p7_1980l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1982_1, c7_1982_2, c7_1982_3, c7_1982_4, c7_1982_5, c7_1982_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1984_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1978l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1984_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1978l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1984_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1978l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1984_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1978l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1984_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1978l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1984 :
    hubcapFit theRedpart rf7 p7_1978l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1984_1, c7_1984_2, c7_1984_3, c7_1984_4, c7_1984_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1991_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1990r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1991_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1990r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1991_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1990r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1991_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1990r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1991_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1990r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1991_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1990r) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1991 :
    hubcapFit theRedpart rf7 p7_1990r
    (Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1991_1, c7_1991_2, c7_1991_3, c7_1991_4, c7_1991_5, c7_1991_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1992_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1990l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1992_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1990l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1992_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1990l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1992_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1990l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1992_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1990l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1992 :
    hubcapFit theRedpart rf7 p7_1990l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1992_1, c7_1992_2, c7_1992_3, c7_1992_4, c7_1992_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1998_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1997r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1998_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1997r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1998_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1997r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1998_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1997r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1998_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1997r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1998_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1997r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1998 :
    hubcapFit theRedpart rf7 p7_1997r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1998_1, c7_1998_2, c7_1998_3, c7_1998_4, c7_1998_5, c7_1998_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1999_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1997l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1999_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1997l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1999_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1997l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1999_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1997l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1999_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1997l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1999 :
    hubcapFit theRedpart rf7 p7_1997l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1999_1, c7_1999_2, c7_1999_3, c7_1999_4, c7_1999_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2001_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1996l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2001_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1996l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2001_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1996l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2001_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1996l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2001_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1996l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2001_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1996l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2001 :
    hubcapFit theRedpart rf7 p7_1996l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2001_1, c7_2001_2, c7_2001_3, c7_2001_4, c7_2001_5, c7_2001_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2003_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1994l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2003_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1994l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2003_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1994l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2003_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1994l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2003_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1994l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2003 :
    hubcapFit theRedpart rf7 p7_1994l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2003_1, c7_2003_2, c7_2003_3, c7_2003_4, c7_2003_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2005_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1988l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2005_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1988l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2005_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1988l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2005_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1988l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2005 :
    hubcapFit theRedpart rf7 p7_1988l
    (Hubcap.one 6 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2005_1, c7_2005_2, c7_2005_3, c7_2005_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2006_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1987l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2006_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1987l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2006_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1987l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2006_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1987l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2006_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1987l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2006_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1987l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2006 :
    hubcapFit theRedpart rf7 p7_1987l
    (Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2006_1, c7_2006_2, c7_2006_3, c7_2006_4, c7_2006_5, c7_2006_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2017_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2016r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2017_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2016r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2017_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2016r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2017_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2016r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2017_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2016r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2017_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2016r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2017 :
    hubcapFit theRedpart rf7 p7_2016r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2017_1, c7_2017_2, c7_2017_3, c7_2017_4, c7_2017_5, c7_2017_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2018_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2016l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2018_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2016l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2018_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2016l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2018_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2016l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2018_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2016l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2018_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2016l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2018 :
    hubcapFit theRedpart rf7 p7_2016l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2018_1, c7_2018_2, c7_2018_3, c7_2018_4, c7_2018_5, c7_2018_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2020_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2015l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2020_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2015l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2020_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2015l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2020_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2015l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2020_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2015l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2020_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2015l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2020 :
    hubcapFit theRedpart rf7 p7_2015l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2020_1, c7_2020_2, c7_2020_3, c7_2020_4, c7_2020_5, c7_2020_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2021_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2014l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2021_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2014l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2021_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2014l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2021_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2014l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2021_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2014l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2021_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2014l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2021_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2014l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2021 :
    hubcapFit theRedpart rf7 p7_2014l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2021_1, c7_2021_2, c7_2021_3, c7_2021_4, c7_2021_5, c7_2021_6, c7_2021_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2023_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2011l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2023_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2011l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2023_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2011l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2023_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2011l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2023_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2011l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2023_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2011l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2023_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2011l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2023 :
    hubcapFit theRedpart rf7 p7_2011l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2023_1, c7_2023_2, c7_2023_3, c7_2023_4, c7_2023_5, c7_2023_6, c7_2023_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2025_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2010l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2025_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2010l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2025_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2010l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2025_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2010l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2025_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2010l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2025_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2010l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2025_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2010l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2025 :
    hubcapFit theRedpart rf7 p7_2010l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2025_1, c7_2025_2, c7_2025_3, c7_2025_4, c7_2025_5, c7_2025_6, c7_2025_7]

end FourColor
