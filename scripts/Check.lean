import FourColor

/-! Fails the build if any `FourColor` declaration is a `sorry` or depends on an
axiom beyond `propext`, `Classical.choice` and `Quot.sound`. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  let mut n := 0
  for (c, _) in env.constants.toList do
    if (`FourColor).isPrefixOf c && !c.isInternal then
      n := n + 1
      for a in (← liftCoreM <| collectAxioms c) do
        unless allowed.contains a do bad := bad.push (c, a)
  unless bad.isEmpty do
    throwError "non-standard axiom dependencies: {bad}"
  -- a per-module tally, so that progress is visible at a glance
  let mut tally : Std.HashMap Name Nat := {}
  for (c, _) in env.constants.toList do
    if (`FourColor).isPrefixOf c && !c.isInternal then
      if let some m := env.getModuleFor? c then
        tally := tally.insert m ((tally.getD m 0) + 1)
  let rows := tally.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  -- A clean run must not be mistaken for a finished proof: report explicitly
  -- whether the theorem itself is present, and check it by name if so.  Without
  -- this, an empty or partial build passes the axiom check in silence.
  let goal : Name := `FourColor.fourColorTheorem
  let status ←
    if env.contains goal then do
      let axs ← liftCoreM <| collectAxioms goal
      let extra := axs.filter (fun a => !allowed.contains a)
      if extra.isEmpty then
        pure s!"THEOREM PROVED: {goal} depends only on {axs.toList}"
      else
        throwError "{goal} depends on non-standard axioms: {extra}"
    else
      pure s!"THEOREM OUTSTANDING: {goal} is not in the build \
(the checks below cover only what is present)"
  let mut msg := s!"{status}\nchecked {n} FourColor declarations: no sorries, no extra axioms\n"
  for (m, k) in rows do
    msg := msg ++ s!"  {m}: {k}\n"
  logInfo msg
