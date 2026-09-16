import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 40 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1892_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1884l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1892_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1884l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1892_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1884l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1892_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1884l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1892_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1884l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1892_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1884l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1892 :
    hubcapFit theRedpart rf9 p9_1884l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1892_1, c9_1892_2, c9_1892_3, c9_1892_4, c9_1892_5, c9_1892_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1896_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1895r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1896_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1895r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1896_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1895r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1896_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1895r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1896_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1895r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1896_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1895r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1896_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1895r) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1896 :
    hubcapFit theRedpart rf9 p9_1895r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1896_1, c9_1896_2, c9_1896_3, c9_1896_4, c9_1896_5, c9_1896_6, c9_1896_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1897_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1895l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1897_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1897_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1897_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1897_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1895l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1897_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1895l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1897_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1895l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1897 :
    hubcapFit theRedpart rf9 p9_1895l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1897_1, c9_1897_2, c9_1897_3, c9_1897_4, c9_1897_5, c9_1897_6, c9_1897_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1899_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1894l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1899_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1899_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1899_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1894l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1899_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1894l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1899_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1894l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1899_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1894l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1899_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1894l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1899 :
    hubcapFit theRedpart rf9 p9_1894l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1899_1, c9_1899_2, c9_1899_3, c9_1899_4, c9_1899_5, c9_1899_6, c9_1899_7, c9_1899_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1901_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1893l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1901_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1893l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1901_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1893l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1901_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1893l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1901_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1893l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1901_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1893l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1901_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1893l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1901_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1893l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1901 :
    hubcapFit theRedpart rf9 p9_1893l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1901_1, c9_1901_2, c9_1901_3, c9_1901_4, c9_1901_5, c9_1901_6, c9_1901_7, c9_1901_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1908_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1907r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1908_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1907r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1908_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1907r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1908_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1907r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1908_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1907r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1908_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1907r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1908_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1907r) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1908 :
    hubcapFit theRedpart rf9 p9_1907r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1908_1, c9_1908_2, c9_1908_3, c9_1908_4, c9_1908_5, c9_1908_6, c9_1908_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1909_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1907l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1909_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1907l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1909_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1907l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1909_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1907l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1909_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1907l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1909_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1907l) (hubSubn 9 7 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1909_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1907l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1909 :
    hubcapFit theRedpart rf9 p9_1907l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1909_1, c9_1909_2, c9_1909_3, c9_1909_4, c9_1909_5, c9_1909_6, c9_1909_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1911_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1906l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1911_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1906l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1911_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1906l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1911_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1906l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1911_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1906l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1911_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1906l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1911_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1906l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1911_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1906l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1911 :
    hubcapFit theRedpart rf9 p9_1906l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1911_1, c9_1911_2, c9_1911_3, c9_1911_4, c9_1911_5, c9_1911_6, c9_1911_7, c9_1911_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1913_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1905l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1913_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1905l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1913_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1905l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1913_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1905l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1913_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1905l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1913_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1905l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1913_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1905l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1913 :
    hubcapFit theRedpart rf9 p9_1905l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1913_1, c9_1913_2, c9_1913_3, c9_1913_4, c9_1913_5, c9_1913_6, c9_1913_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1915_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1904l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1915_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1904l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1915_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1904l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1915_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1904l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1915_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1904l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1915_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1904l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1915_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1904l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1915 :
    hubcapFit theRedpart rf9 p9_1904l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1915_1, c9_1915_2, c9_1915_3, c9_1915_4, c9_1915_5, c9_1915_6, c9_1915_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1917_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1881l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1917_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1881l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1917_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1881l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1917_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1881l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1917_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1881l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1917_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1881l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1917_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1881l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1917_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1881l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1917_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1881l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1917 :
    hubcapFit theRedpart rf9 p9_1881l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1917_1, c9_1917_2, c9_1917_3, c9_1917_4, c9_1917_5, c9_1917_6, c9_1917_7, c9_1917_8, c9_1917_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1925_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1924r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1925_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1924r) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1925_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1924r) (hubSubn 9 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1925_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1924r) (hubSubn 9 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1925_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1924r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1925 :
    hubcapFit theRedpart rf9 p9_1924r
    (Hubcap.one 8 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1925_1, c9_1925_2, c9_1925_3, c9_1925_4, c9_1925_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1926_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1924l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1926_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1924l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1926_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1924l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1926_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1924l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1926_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1924l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1926_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1924l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1926_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1924l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1926 :
    hubcapFit theRedpart rf9 p9_1924l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1926_1, c9_1926_2, c9_1926_3, c9_1926_4, c9_1926_5, c9_1926_6, c9_1926_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1928_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1922l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1928_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1922l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1928_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1922l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1928_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1922l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1928_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1922l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1928_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1922l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1928 :
    hubcapFit theRedpart rf9 p9_1922l
    (Hubcap.one 0 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1928_1, c9_1928_2, c9_1928_3, c9_1928_4, c9_1928_5, c9_1928_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1930_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1930_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1930_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1930_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1920l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1930_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1920l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1930_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1920l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1930 :
    hubcapFit theRedpart rf9 p9_1920l
    (Hubcap.one 0 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1930_1, c9_1930_2, c9_1930_3, c9_1930_4, c9_1930_5, c9_1930_6]

end FourColor
