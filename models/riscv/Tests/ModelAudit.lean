import LeanPaperStock
import Lean
open Lean Elab Command
set_option maxHeartbeats 10000000
#check LeanPaperStock.Functions.execute
#check LeanPaperStock.Functions.try_step
#check LeanPaperStock.Functions.tick_clock
#check LeanPaperStock.Functions.sail_model_init
#check LeanPaperStock.Functions.init_model
#check LeanPaperStock.Functions.init_boot_requirements
run_cmd do
  let env := (← getEnv).setExporting false
  if env.header.moduleNames.contains `LeanPaperStock.FakeReal then
    throwError "FakeReal is imported into the packaged model"
  let roots := #[``LeanPaperStock.Functions.execute, ``LeanPaperStock.Functions.try_step,
    ``LeanPaperStock.Functions.tick_clock, ``LeanPaperStock.Functions.sail_model_init,
    ``LeanPaperStock.Functions.init_model, ``LeanPaperStock.Functions.init_boot_requirements]
  for root in roots do
    let axioms ← liftCoreM (collectAxioms root)
    logInfo m!"{root} axioms: {axioms}"
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "custom axiom {ax}"
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut checked : Nat := 0
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      let some info := env.find? name | throwError "missing {name}"
      if (name.toString.splitOn "UnboundPureHooks").length > 1 ||
         (name.toString.splitOn "UnboundEffectfulHooks").length > 1 then
        throwError "unbound hook in combined type/body cone: {name}"
      let isModelOrRuntime := match env.getModuleIdxFor? name with
        | some idx =>
          let m := env.header.moduleNames[idx.toNat]!.toString
          m == "Sail" || m.startsWith "Sail." || m == "LeanPaperStock" || m.startsWith "LeanPaperStock."
        | none => false
      if isModelOrRuntime then
        checked := checked + 1
        if info.isPartial || info.isUnsafe then throwError "partial/unsafe {name}"
        if (Compiler.getImplementedBy? env name).isSome then throwError "implemented_by {name}"
        if (getExternAttrData? env name).isSome then throwError "extern {name}"
        if info matches .opaqueInfo _ then
          unless ← liftTermElabM (Meta.isProp info.type) do
            throwError "opaque data {name}"
      pending := pending ++ info.type.getUsedConstants
      if let .inductInfo value := info then
        pending := pending ++ value.ctors.toArray
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  -- A checked dependency guard for this pinned generated model. This is separate
  -- from the still-required cross-backend event correspondence proof.
  if seen.contains ``Sail.ConcurrencyInterfaceV1.Free.PreSail.choose then
    throwError "an entry point depends on the free choice primitive"
  logInfo m!"PASS combined transitive types and bodies: {seen.size}; model/runtime inspected: {checked}; no unbound hooks, choice primitive, or FakeReal import"

/- Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account. -/
