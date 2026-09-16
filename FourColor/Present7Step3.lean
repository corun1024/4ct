import FourColor.Present7Step2
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 3 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1262 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1238 p7_1258r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1261

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1264 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1238 p7_1256r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1263
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step1262 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1267 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1238 p7_1254r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1266
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1265
  intro _
  exact s7_step1264 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1269 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1198 p7_1198l := by
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 0 <|
         Hubcap.two 3 4 2 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1268
    intro _
    exact s7_step1267 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1
  intro _
  exact s7_step1253 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1280 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L4_1 : Successful q7_1274) :
    SucceedsIn q7_1197 p7_1276r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1279

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1284 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1274 p7_1274l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1283
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1282

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1286 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1197 p7_1272r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1285
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1284 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro L4_1
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1280 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1288 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1197 p7_1270r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1287
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1286 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1294 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1270 p7_1290r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1293

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1310 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1290 p7_1306r := by
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1309
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1308

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1312 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1290 p7_1305r := by
  refine succeed_by_split .fan1 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1311
  intro _
  exact s7_step1310 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1314 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1290 p7_1304r := by
  refine succeed_by_split .fan1 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1313
  intro _
  exact s7_step1312 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1316 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1290 p7_1302r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1315
  intro _
  refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1314 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1318 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1290 p7_1301r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1317
  intro _
  exact s7_step1316 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1320 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1290 p7_1299r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1319
  intro _
  refine succeed_by_split .fan2 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1318 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1322 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1290 p7_1297r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 5 2 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1321
  intro _
  exact s7_step1320 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1324 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1290 p7_1295r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 1 4 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1323
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1322 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1326 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1270 p7_1289r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 3 <|
         Hubcap.one 2 1 <|
         Hubcap.one 3 0 <|
         Hubcap.one 5 0 <|
         Hubcap.two 4 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1325
    intro _
    exact s7_step1324 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro _
  exact s7_step1294 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1328 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1197 p7_1197l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 0 <|
         Hubcap.one 4 0 <|
         Hubcap.two 1 3 4 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1327
    intro _
    exact s7_step1326 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro _
  exact s7_step1288 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1329 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_885 p7_1104r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
    · exact s7_step1328 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
    intro L3_1
    refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact s7_step1269 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1
    intro _
    refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s7_step1237 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1
    intro L3_2
    exact s7_step1214 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1 L3_2
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step1196 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1342 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1104 p7_1338r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1341

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1344 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1104 p7_1336r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1343
  intro _
  exact s7_step1342 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1347 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1104 p7_1334r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1346
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1345
  intro _
  exact s7_step1344 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1354 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1334 p7_1350r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1353
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1352

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1357 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1334 p7_1348r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1356
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1355
  intro _
  exact s7_step1354 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1359 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1104 p7_1333r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 1 <|
         Hubcap.one 4 1 <|
         Hubcap.one 5 2 <|
         Hubcap.one 6 1 <|
         Hubcap.two 2 3 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1358
    intro _
    exact s7_step1357 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1
  intro _
  exact s7_step1347 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1368 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1332 p7_1364r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1367
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 2 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1366

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1370 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1332 p7_1362r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1369
  intro _
  exact s7_step1368 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1377 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1361 p7_1373r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1376
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1375

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1379 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1361 p7_1371r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1378
  intro _
  exact s7_step1377 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1381 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1332 p7_1360r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 6 1 <|
         Hubcap.two 4 5 2 <|
         Hubcap.two 1 2 4 <|
         Hubcap.two 1 3 3 <|
         Hubcap.two 2 3 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1380
    intro _
    exact s7_step1379 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1370 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1388 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1360 p7_1383r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1387
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1386

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1392 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1383 p7_1383l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1391
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1390

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1394 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1360 p7_1360l := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1393
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s7_step1392 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1
  intro _
  exact s7_step1388 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1402 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1331 p7_1398r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 6 4 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1401
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1400

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1405 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1331 p7_1396r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 6 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1404
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1403
  intro _
  exact s7_step1402 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1410 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1396 p7_1406r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 1 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1409
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1408

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1412 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1331 p7_1395r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.two 0 2 3 <|
         Hubcap.two 1 3 3 <|
         Hubcap.two 4 5 2 <|
         Hubcap.two 4 6 3 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1411
    intro _
    exact s7_step1410 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1
  intro _
  exact s7_step1405 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1420 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1395 p7_1416r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1419
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1418

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1422 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1395 p7_1414r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1421
  intro _
  exact s7_step1420 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1425 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1395 p7_1395l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 6 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1424
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1423
  intro _
  exact s7_step1422 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1426 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L3_1 : Successful q7_1330) :
    SucceedsIn q7_1104 p7_1330r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact s7_step1425 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1
    intro _
    exact s7_step1412 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1
  intro _
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact s7_step1394 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1
    intro _
    exact s7_step1381 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1359 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1436 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1330 p7_1432r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1435
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1434

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1438 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1330 p7_1430r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1437
  intro _
  exact s7_step1436 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1442 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1430 p7_1430l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1441
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1440

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1444 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1330 p7_1428r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1443
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1442 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3
  intro _
  exact s7_step1438 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1451 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1428 p7_1447r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1450
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1449

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1454 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1428 p7_1445r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1453
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1452
  intro _
  exact s7_step1451 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1456 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1330 p7_1427r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 2 0 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 1 <|
         Hubcap.two 0 1 5 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1455
    intro _
    exact s7_step1454 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3
  intro _
  exact s7_step1444 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1468 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1427 p7_1464r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1467
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1466

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1470 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1427 p7_1462r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 5 1 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1469
  intro _
  exact s7_step1468 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1473 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1427 p7_1460r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1472
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1471
  intro _
  exact s7_step1470 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1476 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1427 p7_1458r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1475
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1474
  intro _
  exact s7_step1473 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1481 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1458 p7_1477r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 2 5 2 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1480
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1479

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1483 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1427 p7_1457r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 1 <|
         Hubcap.two 0 4 3 <|
         Hubcap.two 2 3 2 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1482
    intro _
    exact s7_step1481 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3
  intro _
  exact s7_step1476 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1488 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1457 p7_1484r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1487
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1486

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1490 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1427 p7_1427l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 1 <|
         Hubcap.one 5 0 <|
         Hubcap.two 2 3 2 <|
         Hubcap.two 4 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1489
    intro _
    exact s7_step1488 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3
  intro _
  exact s7_step1483 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1498 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1103 p7_1494r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1497
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1496

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1504 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1494 p7_1500r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1503
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1502

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1506 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1494 p7_1494l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1505
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1504 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1512 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1492 p7_1508r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1511
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1510

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1515 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1492 p7_1492l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1514
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1513
  intro _
  exact s7_step1512 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1516 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_1103 p7_1103l := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1515 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1506 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3
  intro _
  exact s7_step1498 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1517 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102) :
    SucceedsIn q7_885 p7_1102r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s7_step1516 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
      · exact s7_step1490 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3
      intro _
      exact s7_step1456 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3
    intro L3_1
    exact s7_step1426 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L3_1
  intro L2_4
  exact s7_step1329 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1527 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1102 p7_1523r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1526
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1525

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1531 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1523 p7_1523l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 2 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1530
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1529

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1533 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1102 p7_1521r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1532
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact s7_step1531 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  exact s7_step1527 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1539 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1520 p7_1535r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1538
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1537

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1541 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1102 p7_1519r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 1 <|
         Hubcap.one 2 0 <|
         Hubcap.two 3 4 3 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1540
    intro _
    exact s7_step1539 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.two 0 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1534
  intro _
  exact s7_step1533 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1548 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1518 p7_1544r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 2 6 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1547
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 0 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 1 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1546

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1551 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1518 p7_1518l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1550
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1549
  intro _
  exact s7_step1548 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1552 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1102 p7_1102l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1551 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1542
  intro _
  exact s7_step1541 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1563 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1101 p7_1559r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1562
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1561

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1565 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1101 p7_1558r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1564
  intro _
  exact s7_step1563 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1567 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1101 p7_1556r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1566
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1565 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1574 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1556 p7_1570r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1573
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1572

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1576 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1556 p7_1569r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1575
  intro _
  exact s7_step1574 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1578 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1556 p7_1568r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1577
  intro _
  exact s7_step1576 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1580 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1101 p7_1555r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.one 3 2 <|
         Hubcap.one 4 0 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1579
    intro _
    exact s7_step1578 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  exact s7_step1567 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1586 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1554 p7_1582r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1585
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1584

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1588 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1101 p7_1553r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.two 3 4 2 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1587
    intro _
    exact s7_step1586 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1581
  intro _
  exact s7_step1580 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1603 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L3_1 : Successful q7_1593) :
    SucceedsIn q7_1100 p7_1599r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1608 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L3_1 : Successful q7_1593) :
    SucceedsIn q7_1598 p7_1604r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1607
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1606

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1610 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L3_1 : Successful q7_1593) :
    SucceedsIn q7_1100 p7_1597r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 2 1 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 0 <|
         Hubcap.two 0 1 5 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1609
    intro _
    exact s7_step1608 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L3_1
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step1603 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1613 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L3_1 : Successful q7_1593) :
    SucceedsIn q7_1100 p7_1595r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1612
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1611
  intro _
  exact s7_step1610 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1622 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L3_1 : Successful q7_1593) :
    SucceedsIn q7_1594 p7_1618r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1621

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1625 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L3_1 : Successful q7_1593) :
    SucceedsIn q7_1594 p7_1616r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1624
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1623
  intro _
  exact s7_step1622 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1628 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L3_1 : Successful q7_1593) :
    SucceedsIn q7_1594 p7_1594l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1627
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1626
  intro _
  exact s7_step1625 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1629 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L3_1 : Successful q7_1593) :
    SucceedsIn q7_1100 p7_1593r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1628 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L3_1
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1614
  intro _
  exact s7_step1613 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1639 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1593 p7_1635r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1638
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1637

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1641 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1593 p7_1634r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1640
  intro _
  exact s7_step1639 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1647 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1633 p7_1643r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1646
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1645

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1650 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1633 p7_1633l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1649
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1648
  intro _
  exact s7_step1647 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1652 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1593 p7_1631r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1651
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact s7_step1650 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1641 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1655 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1593 p7_1593l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1654
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1653
  intro _
  exact s7_step1652 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1657 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1100 p7_1591r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 0 2 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1656
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact s7_step1655 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro L3_1
  exact s7_step1629 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1666 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1591 p7_1662r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1665
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1664

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1669 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1591 p7_1660r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 2 3 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1668
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 5 2 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 3 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1667
  intro _
  exact s7_step1666 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1672 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1591 p7_1658r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1671
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1670
  intro _
  exact s7_step1669 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1674 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1100 p7_1590r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 3 0 <|
         Hubcap.two 0 4 3 <|
         Hubcap.two 1 2 2 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1673
    intro _
    exact s7_step1672 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  exact s7_step1657 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1677 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1100 p7_1100l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1676
  intro _
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1675
  intro _
  exact s7_step1674 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1678 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_885 p7_1099r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1677 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 true L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step1588 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact s7_step1552 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro L2_3
  exact s7_step1517 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1687 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1099 p7_1683r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1686
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1685

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1690 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1099 p7_1681r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1689
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1688
  intro _
  exact s7_step1687 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1698 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1680 p7_1694r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1697
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1696

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1701 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1680 p7_1692r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1700
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1699
  intro _
  exact s7_step1698 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1703 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1099 p7_1679r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 5 0 <|
         Hubcap.one 6 2 <|
         Hubcap.two 1 2 2 <|
         Hubcap.two 3 4 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1702
    intro _
    exact s7_step1701 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 5 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 6 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1691
  intro _
  exact s7_step1690 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1705 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_885 p7_1098r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 2 <|
         Hubcap.one 5 0 <|
         Hubcap.one 6 2 <|
         Hubcap.two 0 2 3 <|
         Hubcap.two 3 4 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1704
    intro _
    exact s7_step1703 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  exact s7_step1678 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1719 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1098 p7_1715r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1718
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1717

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1721 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1098 p7_1713r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1720
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1719 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1728 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1713 p7_1724r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1727
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1726

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1730 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1713 p7_1722r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1729
  intro _
  exact s7_step1728 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1732 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1098 p7_1712r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 1 <|
         Hubcap.one 2 1 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 0 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1731
    intro _
    exact s7_step1730 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  exact s7_step1721 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1734 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1098 p7_1711r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1733
  intro _
  exact s7_step1732 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1739 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1710 p7_1735r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1738
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 2 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1737

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1741 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1098 p7_1709r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 3 1 <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 0 <|
         Hubcap.one 6 4 <|
         Hubcap.two 1 2 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1740
    intro _
    exact s7_step1739 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1734 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1744 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1098 p7_1707r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1743
  intro _
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1742
  intro _
  exact s7_step1741 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1746 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097) :
    SucceedsIn q7_1098 p7_1098l := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1745
  intro _
  exact s7_step1744 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1761 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1097 p7_1757r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 (-1) <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1760
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1759

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1764 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1097 p7_1755r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1763
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1762
  intro _
  exact s7_step1761 hred L1_1 L1_2 L1_3 L1_4 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1772 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1754 p7_1768r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1771
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1770

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1775 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1754 p7_1766r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1774
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1773
  intro _
  exact s7_step1772 hred L1_1 L1_2 L1_3 L1_4 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1777 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1097 p7_1753r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 1 <|
         Hubcap.two 1 2 3 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1776
    intro _
    exact s7_step1775 hred L1_1 L1_2 L1_3 L1_4 L2_1
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1765
  intro _
  exact s7_step1764 hred L1_1 L1_2 L1_3 L1_4 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1785 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1752 p7_1781r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1784
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1783

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1788 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1752 p7_1779r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1787
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1786
  intro _
  exact s7_step1785 hred L1_1 L1_2 L1_3 L1_4 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1790 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1097 p7_1751r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 2 0 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 1 <|
         Hubcap.two 0 1 4 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1789
    intro _
    exact s7_step1788 hred L1_1 L1_2 L1_3 L1_4 L2_1
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 0 2 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1778
  intro _
  exact s7_step1777 hred L1_1 L1_2 L1_3 L1_4 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1793 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1097 p7_1749r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1792
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1791
  intro _
  exact s7_step1790 hred L1_1 L1_2 L1_3 L1_4 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1796 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_1097 p7_1747r := by
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1795
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1794
  intro _
  exact s7_step1793 hred L1_1 L1_2 L1_3 L1_4 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1798 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096) :
    SucceedsIn q7_885 p7_1096r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 1 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1797
    intro _
    exact s7_step1796 hred L1_1 L1_2 L1_3 L1_4 L2_1
  intro L2_2
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact s7_step1746 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2
  intro _
  exact s7_step1705 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1808 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883) :
    SucceedsIn q7_1096 p7_1804r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1807
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1806

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1811 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883) :
    SucceedsIn q7_1096 p7_1802r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1810
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1809
  intro _
  exact s7_step1808 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1814 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883) :
    SucceedsIn q7_1096 p7_1800r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1813
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1812
  intro _
  exact s7_step1811 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1817 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883) :
    SucceedsIn q7_1096 p7_1096l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1816
  intro _
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1815
  intro _
  exact s7_step1814 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1818 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883) :
    SucceedsIn q7_1 p7_883r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L1_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
    · exact s7_step1817 hred L1_1 L1_2 L1_3 L1_4
    intro L2_1
    exact s7_step1798 hred L1_1 L1_2 L1_3 L1_4 L2_1
  intro L1_5
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L1_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step1095 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1849 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_883 p7_1845r := by
  refine succeed_by_split .fan2 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1848
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1847

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1851 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_883 p7_1844r := by
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1850
  intro _
  exact s7_step1849 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1853 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_883 p7_1841r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1852
  intro _
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1851 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1855 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_883 p7_1840r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1854
  intro _
  exact s7_step1853 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1856 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_883 p7_1836r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1855 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1858 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_883 p7_1834r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1857
  intro _
  exact s7_step1856 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1860 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_883 p7_1833r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1859
  intro _
  exact s7_step1858 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1869 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_1832 p7_1865r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1868
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1867

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1871 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_1832 p7_1864r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1870
  intro _
  exact s7_step1869 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1873 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_1832 p7_1862r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1872
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1871 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1875 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_1832 p7_1832l := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1874
  intro _
  exact s7_step1873 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1883 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_1831 p7_1879r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1882
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1881

end FourColor
