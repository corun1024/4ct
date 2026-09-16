import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 39 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1996_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1996_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1996_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1958l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1996_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1996_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1958l) (hubSubn 8 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1996_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1958l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1996 :
    hubcapFit theRedpart rf8 p8_1958l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1996_1, c8_1996_2, c8_1996_3, c8_1996_4, c8_1996_5, c8_1996_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1997_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1957l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1997_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1997_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1997_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1957l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1997_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1957l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1997_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1957l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1997_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1957l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1997 :
    hubcapFit theRedpart rf8 p8_1957l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1997_1, c8_1997_2, c8_1997_3, c8_1997_4, c8_1997_5, c8_1997_6, c8_1997_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1999_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1955l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1999_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1955l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1999_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1955l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1999_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1955l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1999_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1955l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1999 :
    hubcapFit theRedpart rf8 p8_1955l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1999_1, c8_1999_2, c8_1999_3, c8_1999_4, c8_1999_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2001_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1954l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2001_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1954l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2001_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1954l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2001_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1954l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2001_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1954l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2001_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1954l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2001_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1954l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2001 :
    hubcapFit theRedpart rf8 p8_1954l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2001_1, c8_2001_2, c8_2001_3, c8_2001_4, c8_2001_5, c8_2001_6, c8_2001_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2003_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1953l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2003_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1953l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2003_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1953l) (hubSubn 8 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2003_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1953l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2003_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1953l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2003 :
    hubcapFit theRedpart rf8 p8_1953l
    (Hubcap.one 0 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 4 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2003_1, c8_2003_2, c8_2003_3, c8_2003_4, c8_2003_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2004_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1952l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2004_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1952l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2004_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1952l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2004_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1952l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2004_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1952l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2004_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1952l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2004 :
    hubcapFit theRedpart rf8 p8_1952l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2004_1, c8_2004_2, c8_2004_3, c8_2004_4, c8_2004_5, c8_2004_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2019_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2018r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2019_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2018r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2019_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2018r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2019_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2018r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2019_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2018r) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2019_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2018r) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2019 :
    hubcapFit theRedpart rf8 p8_2018r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2019_1, c8_2019_2, c8_2019_3, c8_2019_4, c8_2019_5, c8_2019_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2020_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2018l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2020_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2018l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2020_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2018l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2020_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2018l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2020_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2018l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2020_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2020_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2020_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2018l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2020 :
    hubcapFit theRedpart rf8 p8_2018l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2020_1, c8_2020_2, c8_2020_3, c8_2020_4, c8_2020_5, c8_2020_6, c8_2020_7, c8_2020_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2022_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2017l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2022_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2017l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2022_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2017l) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2022_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2017l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2022_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2017l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2022 :
    hubcapFit theRedpart rf8 p8_2017l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2022_1, c8_2022_2, c8_2022_3, c8_2022_4, c8_2022_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2023_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2016l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2023_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2016l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2023_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2016l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2023_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2016l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2023_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2016l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2023_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2016l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2023_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2016l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2023 :
    hubcapFit theRedpart rf8 p8_2016l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2023_1, c8_2023_2, c8_2023_3, c8_2023_4, c8_2023_5, c8_2023_6, c8_2023_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2025_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2015l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2025_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2015l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2025_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2015l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2025_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2015l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2025_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2015l) (hubSubn 8 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2025_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2015l) (hubSubn 8 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2025 :
    hubcapFit theRedpart rf8 p8_2015l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2025_1, c8_2025_2, c8_2025_3, c8_2025_4, c8_2025_5, c8_2025_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2027_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2013l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2027_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2013l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2027_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2013l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2027_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2013l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2027_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2013l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2027 :
    hubcapFit theRedpart rf8 p8_2013l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2027_1, c8_2027_2, c8_2027_3, c8_2027_4, c8_2027_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2028_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2012l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2028_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2012l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2028_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2012l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2028_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2012l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2028_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2012l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2028_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2012l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2028 :
    hubcapFit theRedpart rf8 p8_2012l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2028_1, c8_2028_2, c8_2028_3, c8_2028_4, c8_2028_5, c8_2028_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2030_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2010l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2030_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2010l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2030_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2010l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2030_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2010l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2030_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2010l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2030 :
    hubcapFit theRedpart rf8 p8_2010l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2030_1, c8_2030_2, c8_2030_3, c8_2030_4, c8_2030_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2032_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2009l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2032_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2009l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2032_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2009l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2032_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2009l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2032_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2009l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2032_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2009l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2032_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2009l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2032_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2009l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2032 :
    hubcapFit theRedpart rf8 p8_2009l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2032_1, c8_2032_2, c8_2032_3, c8_2032_4, c8_2032_5, c8_2032_6, c8_2032_7, c8_2032_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2034_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2008l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2034_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2008l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2034_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2008l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2034_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2008l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2034_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2008l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2034_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2008l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2034_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2008l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2034 :
    hubcapFit theRedpart rf8 p8_2008l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2034_1, c8_2034_2, c8_2034_3, c8_2034_4, c8_2034_5, c8_2034_6, c8_2034_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2036_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2007l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2036_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2007l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2036_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2036_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2007l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2036_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2007l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2036_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2036_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2007l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2036 :
    hubcapFit theRedpart rf8 p8_2007l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2036_1, c8_2036_2, c8_2036_3, c8_2036_4, c8_2036_5, c8_2036_6, c8_2036_7]

end FourColor
