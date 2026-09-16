import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 37 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1859_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1858l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1859_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1858l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1859_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1858l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1859_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1858l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1859_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1858l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1859_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1858l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1859 :
    hubcapFit theRedpart rf8 p8_1858l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1859_1, c8_1859_2, c8_1859_3, c8_1859_4, c8_1859_5, c8_1859_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1863_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1862l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1863_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1862l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1863_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1862l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1863_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1862l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1863_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1862l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1863_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1862l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1863 :
    hubcapFit theRedpart rf8 p8_1862l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1863_1, c8_1863_2, c8_1863_3, c8_1863_4, c8_1863_5, c8_1863_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1865_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1862r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1865_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1862r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1865_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1862r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1865_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1862r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1865_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1862r) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1865_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1862r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1865 :
    hubcapFit theRedpart rf8 p8_1862r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1865_1, c8_1865_2, c8_1865_3, c8_1865_4, c8_1865_5, c8_1865_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1868_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1861r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1868_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1861r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1868_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1861r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1868_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1861r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1868_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1861r) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1868_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1861r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1868 :
    hubcapFit theRedpart rf8 p8_1861r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1868_1, c8_1868_2, c8_1868_3, c8_1868_4, c8_1868_5, c8_1868_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1873_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1815l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1873_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1815l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1873_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1815l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1873_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1873_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1815l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1873_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1873_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1815l) (hubSubn 8 7 6) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1873 :
    hubcapFit theRedpart rf8 p8_1815l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.two 6 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1873_1, c8_1873_2, c8_1873_3, c8_1873_4, c8_1873_5, c8_1873_6, c8_1873_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1879_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1878l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1879_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1878l) (hubSubn 8 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1879_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1878l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1879_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1878l) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1879_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1878l) (hubSubn 8 6 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1879_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1878l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1879 :
    hubcapFit theRedpart rf8 p8_1878l
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1879_1, c8_1879_2, c8_1879_3, c8_1879_4, c8_1879_5, c8_1879_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1881_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1878r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1881_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1878r) (hubSubn 8 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1881_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1878r) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1881_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1878r) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1881_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1878r) (hubSubn 8 6 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1881_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1878r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1881 :
    hubcapFit theRedpart rf8 p8_1878r
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1881_1, c8_1881_2, c8_1881_3, c8_1881_4, c8_1881_5, c8_1881_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1885_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1884l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1885_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1884l) (hubSubn 8 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1885_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1884l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1885_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1884l) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1885_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1884l) (hubSubn 8 6 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1885_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1884l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1885 :
    hubcapFit theRedpart rf8 p8_1884l
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1885_1, c8_1885_2, c8_1885_3, c8_1885_4, c8_1885_5, c8_1885_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1887_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1884r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1887_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1884r) (hubSubn 8 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1887_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1884r) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1887_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1884r) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1887_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1884r) (hubSubn 8 6 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1887_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1884r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1887 :
    hubcapFit theRedpart rf8 p8_1884r
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1887_1, c8_1887_2, c8_1887_3, c8_1887_4, c8_1887_5, c8_1887_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1892_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1891l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1892_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1891l) (hubSubn 8 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1892_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1891l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1892_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1891l) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1892_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1891l) (hubSubn 8 6 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1892_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1891l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1892 :
    hubcapFit theRedpart rf8 p8_1891l
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1892_1, c8_1892_2, c8_1892_3, c8_1892_4, c8_1892_5, c8_1892_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1894_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1891r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1894_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1891r) (hubSubn 8 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1894_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1891r) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1894_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1891r) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1894_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1891r) (hubSubn 8 6 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1894_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1891r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1894 :
    hubcapFit theRedpart rf8 p8_1891r
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1894_1, c8_1894_2, c8_1894_3, c8_1894_4, c8_1894_5, c8_1894_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1899_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1898l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1899_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1898l) (hubSubn 8 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1899_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1898l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1899_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1898l) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1899_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1898l) (hubSubn 8 6 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1899_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1898l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1899 :
    hubcapFit theRedpart rf8 p8_1898l
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1899_1, c8_1899_2, c8_1899_3, c8_1899_4, c8_1899_5, c8_1899_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1901_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1898r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1901_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1898r) (hubSubn 8 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1901_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1898r) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1901_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1898r) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1901_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1898r) (hubSubn 8 6 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1901_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1898r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1901 :
    hubcapFit theRedpart rf8 p8_1898r
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1901_1, c8_1901_2, c8_1901_3, c8_1901_4, c8_1901_5, c8_1901_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1929_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1928r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1929_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1928r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1929_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1928r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1929_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1928r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1929_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1928r) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1929 :
    hubcapFit theRedpart rf8 p8_1928r
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1929_1, c8_1929_2, c8_1929_3, c8_1929_4, c8_1929_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1930_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1928l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1930_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1928l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1930_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1928l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1930_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1928l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1930_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1928l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1930_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1928l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1930 :
    hubcapFit theRedpart rf8 p8_1928l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1930_1, c8_1930_2, c8_1930_3, c8_1930_4, c8_1930_5, c8_1930_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1932_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1926l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1932_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1926l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1932_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1926l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1932_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1926l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1932_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1926l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1932_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1926l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1932_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1926l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1932 :
    hubcapFit theRedpart rf8 p8_1926l
    (Hubcap.one 0 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1932_1, c8_1932_2, c8_1932_3, c8_1932_4, c8_1932_5, c8_1932_6, c8_1932_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1934_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1925l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1934_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1925l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1934_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1925l) (hubSubn 8 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1934_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1925l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1934_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1925l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1934 :
    hubcapFit theRedpart rf8 p8_1925l
    (Hubcap.one 0 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1934_1, c8_1934_2, c8_1934_3, c8_1934_4, c8_1934_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1935_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1924l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1935_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1924l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1935_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1924l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1935_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1924l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1935_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1924l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1935 :
    hubcapFit theRedpart rf8 p8_1924l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1935_1, c8_1935_2, c8_1935_3, c8_1935_4, c8_1935_5]

end FourColor
