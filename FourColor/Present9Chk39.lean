import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 39 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1832_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1829r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1832_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1829r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1832_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1829r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1832_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1829r) (hubSubn 9 4 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1832_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1829r) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1832_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1829r) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1832 :
    hubcapFit theRedpart rf9 p9_1829r
    (Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1832_1, c9_1832_2, c9_1832_3, c9_1832_4, c9_1832_5, c9_1832_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1837_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1836l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1837_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1836l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1837_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1836l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1837_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1836l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1837_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1836l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1837_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1836l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1837_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1836l) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1837 :
    hubcapFit theRedpart rf9 p9_1836l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1837_1, c9_1837_2, c9_1837_3, c9_1837_4, c9_1837_5, c9_1837_6, c9_1837_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1840_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1839l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1840_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1839l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1840_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1839l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1840_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1840_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1840_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1839l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1840_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1839l) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1840 :
    hubcapFit theRedpart rf9 p9_1839l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1840_1, c9_1840_2, c9_1840_3, c9_1840_4, c9_1840_5, c9_1840_6, c9_1840_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1842_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1839r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1842_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1839r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1842_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1839r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1842_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1839r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1842_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1839r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1842_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1839r) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1842_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1839r) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1842 :
    hubcapFit theRedpart rf9 p9_1839r
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1842_1, c9_1842_2, c9_1842_3, c9_1842_4, c9_1842_5, c9_1842_6, c9_1842_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1849_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1848l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1849_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1848l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1849_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1848l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1849_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1848l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1849_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1848l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1849_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1848l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1849_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1848l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1849_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1848l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1849 :
    hubcapFit theRedpart rf9 p9_1848l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1849_1, c9_1849_2, c9_1849_3, c9_1849_4, c9_1849_5, c9_1849_6, c9_1849_7, c9_1849_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1851_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1848r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1851_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1848r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1851_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1848r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1851_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1848r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1851_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1848r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1851_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1848r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1851_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1848r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1851_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1848r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1851 :
    hubcapFit theRedpart rf9 p9_1848r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1851_1, c9_1851_2, c9_1851_3, c9_1851_4, c9_1851_5, c9_1851_6, c9_1851_7, c9_1851_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1855_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1854l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1855_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1854l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1855_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1854l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1855_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1854l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1855_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1854l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1855_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1854l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1855_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1854l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1855_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1854l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1855 :
    hubcapFit theRedpart rf9 p9_1854l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1855_1, c9_1855_2, c9_1855_3, c9_1855_4, c9_1855_5, c9_1855_6, c9_1855_7, c9_1855_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1857_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1854r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1857_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1854r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1857_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1854r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1857_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1854r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1857_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1854r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1857_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1854r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1857_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1854r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1857_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1854r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1857 :
    hubcapFit theRedpart rf9 p9_1854r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1857_1, c9_1857_2, c9_1857_3, c9_1857_4, c9_1857_5, c9_1857_6, c9_1857_7, c9_1857_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1862_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1861l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1862_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1861l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1862_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1861l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1862_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1861l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1862_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1861l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1862_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1861l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1862_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1861l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1862 :
    hubcapFit theRedpart rf9 p9_1861l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1862_1, c9_1862_2, c9_1862_3, c9_1862_4, c9_1862_5, c9_1862_6, c9_1862_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1864_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1861r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1864_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1861r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1864_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1861r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1864_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1861r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1864_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1861r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1864_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1861r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1864_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1861r) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1864 :
    hubcapFit theRedpart rf9 p9_1861r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1864_1, c9_1864_2, c9_1864_3, c9_1864_4, c9_1864_5, c9_1864_6, c9_1864_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1868_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1867l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1868_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1867l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1868_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1867l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1868_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1867l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1868_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1867l) (hubSubn 9 6 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1868_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1867l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1868 :
    hubcapFit theRedpart rf9 p9_1867l
    (Hubcap.one 0 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 2 6 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1868_1, c9_1868_2, c9_1868_3, c9_1868_4, c9_1868_5, c9_1868_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1870_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1867r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1870_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1867r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1870_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1867r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1870_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1867r) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1870_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1867r) (hubSubn 9 6 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1870_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1867r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1870 :
    hubcapFit theRedpart rf9 p9_1867r
    (Hubcap.one 0 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 2 6 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1870_1, c9_1870_2, c9_1870_3, c9_1870_4, c9_1870_5, c9_1870_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1887_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1886r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1887_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1886r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1887_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1886r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1887_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1886r) (hubSubn 9 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1887_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1886r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1887_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1886r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1887 :
    hubcapFit theRedpart rf9 p9_1886r
    (Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1887_1, c9_1887_2, c9_1887_3, c9_1887_4, c9_1887_5, c9_1887_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1888_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1888_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1886l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1888_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1888_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1886l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1888_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1888_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1886l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1888_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1886l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1888 :
    hubcapFit theRedpart rf9 p9_1886l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1888_1, c9_1888_2, c9_1888_3, c9_1888_4, c9_1888_5, c9_1888_6, c9_1888_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1890_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1885l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1890_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1885l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1890_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1885l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1890_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1885l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1890_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1885l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1890_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1885l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1890_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1885l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1890 :
    hubcapFit theRedpart rf9 p9_1885l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1890_1, c9_1890_2, c9_1890_3, c9_1890_4, c9_1890_5, c9_1890_6, c9_1890_7]

end FourColor
