import FourColor.Present9Hub1

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 2 of the arity 9 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1197 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1189r := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact h9_1194 hred _
  intro _
  exact h9_1196 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1198 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1141l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h9_1191 hred _
  intro _
  exact h9_1197 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1202 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1200l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1201

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1204 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1200r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1203

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1205 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1199l := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact h9_1202 hred _
  intro _
  exact h9_1204 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1208 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1206l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1207

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1210 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1206r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1209

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1211 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1199r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact h9_1208 hred _
  intro _
  exact h9_1210 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1212 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1140l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h9_1205 hred _
  intro _
  exact h9_1211 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1216 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1214l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1215

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1218 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1214r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1217

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1219 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1213l := by
  refine succeed_by_split .spoke 0 7 true (by decide +kernel) ?_ ?_
  · exact h9_1216 hred _
  intro _
  exact h9_1218 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1222 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1220l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1221

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1224 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1220r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1223

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1225 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1213r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact h9_1222 hred _
  intro _
  exact h9_1224 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1226 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1139l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h9_1219 hred _
  intro _
  exact h9_1225 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1230 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1228l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1229

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1232 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1228r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1231

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1233 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1227l := by
  refine succeed_by_split .spoke 0 7 true (by decide +kernel) ?_ ?_
  · exact h9_1230 hred _
  intro _
  exact h9_1232 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1236 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1234l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1235

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1238 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1234r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1237

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1239 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1227r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact h9_1236 hred _
  intro _
  exact h9_1238 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1240 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1138l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h9_1233 hred _
  intro _
  exact h9_1239 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1245 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1243l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1244

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1247 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1243r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1246

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1248 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1242l := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact h9_1245 hred _
  intro _
  exact h9_1247 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1251 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1249l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1250

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1253 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1249r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1252

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1254 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1242r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact h9_1251 hred _
  intro _
  exact h9_1253 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1255 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1137l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h9_1248 hred _
  intro _
  exact h9_1254 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1298 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1296l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1297

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1302 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1300l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1301

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1304 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1300r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1303

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1305 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1299l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact h9_1302 hred _
  intro _
  exact h9_1304 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1307 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1299r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1306

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1308 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1296r := by
  refine succeed_by_split .spoke 0 7 true (by decide +kernel) ?_ ?_
  · exact h9_1305 hred _
  intro _
  exact h9_1307 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1309 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_920l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h9_1298 hred _
  intro _
  exact h9_1308 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1430 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1428l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1429

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1432 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1428r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1431

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1433 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1391l := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact h9_1430 hred _
  intro _
  exact h9_1432 hred _

end FourColor
