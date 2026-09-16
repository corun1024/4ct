import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 34 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1857_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1836l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1857_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1836l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1857_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1836l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1857_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1836l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1857_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1836l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1857_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1836l) (hubSubn 7 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1857 :
    hubcapFit theRedpart rf7 p7_1836l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1857_1, c7_1857_2, c7_1857_3, c7_1857_4, c7_1857_5, c7_1857_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1859_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1834l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1859_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1834l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1859_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1834l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1859_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1834l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1859_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1834l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1859_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1834l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1859_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1834l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1859 :
    hubcapFit theRedpart rf7 p7_1834l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1859_1, c7_1859_2, c7_1859_3, c7_1859_4, c7_1859_5, c7_1859_6, c7_1859_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1867_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1866r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1867_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1866r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1867_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1866r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1867_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1866r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1867_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1866r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1867_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1866r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1867 :
    hubcapFit theRedpart rf7 p7_1866r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1867_1, c7_1867_2, c7_1867_3, c7_1867_4, c7_1867_5, c7_1867_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1868_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1866l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1868_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1866l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1868_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1866l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1868_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1866l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1868_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1866l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1868_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1866l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1868 :
    hubcapFit theRedpart rf7 p7_1866l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1868_1, c7_1868_2, c7_1868_3, c7_1868_4, c7_1868_5, c7_1868_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1870_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1870_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1865l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1870_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1865l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1870_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1865l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1870_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1865l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1870_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1865l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1870_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1865l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1870 :
    hubcapFit theRedpart rf7 p7_1865l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1870_1, c7_1870_2, c7_1870_3, c7_1870_4, c7_1870_5, c7_1870_6, c7_1870_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1872_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1863l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1872_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1863l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1872_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1863l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1872_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1863l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1872_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1863l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1872_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1863l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1872 :
    hubcapFit theRedpart rf7 p7_1863l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1872_1, c7_1872_2, c7_1872_3, c7_1872_4, c7_1872_5, c7_1872_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1874_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1862l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1874_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1862l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1874_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1862l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1874_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1862l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1874_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1862l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1874_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1862l) (hubSubn 7 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1874 :
    hubcapFit theRedpart rf7 p7_1862l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1874_1, c7_1874_2, c7_1874_3, c7_1874_4, c7_1874_5, c7_1874_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1881_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1880r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1881_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1880r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1881_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1880r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1881_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1880r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1881_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1880r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1881_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1880r) (hubSubn 7 3 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1881 :
    hubcapFit theRedpart rf7 p7_1880r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1881_1, c7_1881_2, c7_1881_3, c7_1881_4, c7_1881_5, c7_1881_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1882_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1880l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1882_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1880l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1882_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1880l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1882_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1880l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1882_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1880l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1882_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1880l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1882_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1880l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1882 :
    hubcapFit theRedpart rf7 p7_1880l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1882_1, c7_1882_2, c7_1882_3, c7_1882_4, c7_1882_5, c7_1882_6, c7_1882_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1884_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1878l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1884_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1878l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1884_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1878l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1884_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1878l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1884_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1878l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1884_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1878l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1884 :
    hubcapFit theRedpart rf7 p7_1878l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1884_1, c7_1884_2, c7_1884_3, c7_1884_4, c7_1884_5, c7_1884_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1889_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1888r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1889_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1888r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1889_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1888r) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1889_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1888r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1889_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1888r) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1889_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1888r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1889 :
    hubcapFit theRedpart rf7 p7_1888r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1889_1, c7_1889_2, c7_1889_3, c7_1889_4, c7_1889_5, c7_1889_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1890_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1888l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1890_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1888l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1890_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1888l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1890_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1888l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1890_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1888l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1890_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1888l) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1890_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1888l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1890 :
    hubcapFit theRedpart rf7 p7_1888l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1890_1, c7_1890_2, c7_1890_3, c7_1890_4, c7_1890_5, c7_1890_6, c7_1890_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1900_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1899r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1900_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1899r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1900_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1899r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1900_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1899r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1900_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1899r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1900_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1899r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1900_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1899r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1900 :
    hubcapFit theRedpart rf7 p7_1899r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1900_1, c7_1900_2, c7_1900_3, c7_1900_4, c7_1900_5, c7_1900_6, c7_1900_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1902_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1897l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1902_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1897l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1902_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1897l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1902_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1897l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1902_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1897l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1902_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1897l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1902_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1897l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1902 :
    hubcapFit theRedpart rf7 p7_1897l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1902_1, c7_1902_2, c7_1902_3, c7_1902_4, c7_1902_5, c7_1902_6, c7_1902_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1904_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1904_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1894l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1904_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1894l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1904_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1894l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1904_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1894l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1904_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1894l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1904 :
    hubcapFit theRedpart rf7 p7_1894l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1904_1, c7_1904_2, c7_1904_3, c7_1904_4, c7_1904_5, c7_1904_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1922_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1921r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1922_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1921r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1922_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1921r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1922_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1921r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1922_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1921r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1922_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1921r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1922 :
    hubcapFit theRedpart rf7 p7_1921r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1922_1, c7_1922_2, c7_1922_3, c7_1922_4, c7_1922_5, c7_1922_6]

end FourColor
