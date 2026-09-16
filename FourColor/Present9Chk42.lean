import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 42 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1985_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1963l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1985_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1985_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1963l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1985_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1963l) (hubSubn 9 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1985_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1963l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1985_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1963l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1985 :
    hubcapFit theRedpart rf9 p9_1963l
    (Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1985_1, c9_1985_2, c9_1985_3, c9_1985_4, c9_1985_5, c9_1985_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1997_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1996r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1997_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1996r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1997_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1996r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1997_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1996r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1997_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1996r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1997_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1996r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1997_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1996r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1997_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1996r) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1997 :
    hubcapFit theRedpart rf9 p9_1996r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1997_1, c9_1997_2, c9_1997_3, c9_1997_4, c9_1997_5, c9_1997_6, c9_1997_7, c9_1997_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1998_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1998_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1998_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1998_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1996l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1998_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1996l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1998_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1998_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1998_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1996l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1998_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1996l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1998 :
    hubcapFit theRedpart rf9 p9_1996l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1998_1, c9_1998_2, c9_1998_3, c9_1998_4, c9_1998_5, c9_1998_6, c9_1998_7, c9_1998_8, c9_1998_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2000_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1995l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2000_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2000_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2000_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1995l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2000_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1995l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2000_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1995l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2000_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2000_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2000_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1995l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2000 :
    hubcapFit theRedpart rf9 p9_1995l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2000_1, c9_2000_2, c9_2000_3, c9_2000_4, c9_2000_5, c9_2000_6, c9_2000_7, c9_2000_8, c9_2000_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2002_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2002_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2002_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2002_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1994l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2002_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1994l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2002_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1994l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2002_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1994l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2002_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2002_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2002 :
    hubcapFit theRedpart rf9 p9_1994l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2002_1, c9_2002_2, c9_2002_3, c9_2002_4, c9_2002_5, c9_2002_6, c9_2002_7, c9_2002_8, c9_2002_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2004_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1992l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2004_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1992l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2004_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1992l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2004_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1992l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2004_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1992l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2004_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1992l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2004_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1992l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2004_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1992l) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2004 :
    hubcapFit theRedpart rf9 p9_1992l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2004_1, c9_2004_2, c9_2004_3, c9_2004_4, c9_2004_5, c9_2004_6, c9_2004_7, c9_2004_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2006_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1991l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2006_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1991l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2006_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1991l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2006_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1991l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2006_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1991l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2006_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1991l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2006_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1991l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2006_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1991l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2006_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1991l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2006 :
    hubcapFit theRedpart rf9 p9_1991l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2006_1, c9_2006_2, c9_2006_3, c9_2006_4, c9_2006_5, c9_2006_6, c9_2006_7, c9_2006_8, c9_2006_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2008_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1990l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2008_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1990l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2008_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1990l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2008_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1990l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2008_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1990l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2008_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1990l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2008_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1990l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2008_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1990l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2008 :
    hubcapFit theRedpart rf9 p9_1990l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2008_1, c9_2008_2, c9_2008_3, c9_2008_4, c9_2008_5, c9_2008_6, c9_2008_7, c9_2008_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2010_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1988l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2010_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1988l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2010_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1988l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2010_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1988l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2010_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1988l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2010_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1988l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2010_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1988l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2010_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1988l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2010 :
    hubcapFit theRedpart rf9 p9_1988l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2010_1, c9_2010_2, c9_2010_3, c9_2010_4, c9_2010_5, c9_2010_6, c9_2010_7, c9_2010_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2012_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1987l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2012_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1987l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2012_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1987l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2012_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1987l) (hubSubn 9 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2012_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1987l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2012_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1987l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2012 :
    hubcapFit theRedpart rf9 p9_1987l
    (Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2012_1, c9_2012_2, c9_2012_3, c9_2012_4, c9_2012_5, c9_2012_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2014_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2014_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2014_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1960l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2014_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1960l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2014_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2014_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2014_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2014_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1960l) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2014 :
    hubcapFit theRedpart rf9 p9_1960l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2014_1, c9_2014_2, c9_2014_3, c9_2014_4, c9_2014_5, c9_2014_6, c9_2014_7, c9_2014_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2016_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1958l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2016_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2016_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2016_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2016_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2016_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1958l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2016_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1958l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2016 :
    hubcapFit theRedpart rf9 p9_1958l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2016_1, c9_2016_2, c9_2016_3, c9_2016_4, c9_2016_5, c9_2016_6, c9_2016_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2025_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2024r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2025_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2024r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2025_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2024r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2025_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2024r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2025_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2024r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2025_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2024r) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2025_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2024r) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2025 :
    hubcapFit theRedpart rf9 p9_2024r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2025_1, c9_2025_2, c9_2025_3, c9_2025_4, c9_2025_5, c9_2025_6, c9_2025_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2026_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2026_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2026_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2026_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2026_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2026_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2026_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2026_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2024l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2026 :
    hubcapFit theRedpart rf9 p9_2024l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2026_1, c9_2026_2, c9_2026_3, c9_2026_4, c9_2026_5, c9_2026_6, c9_2026_7, c9_2026_8]

end FourColor
