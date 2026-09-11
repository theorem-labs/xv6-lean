import MachCSL.Machine.SpinlockWitnessDefs
import MachCSL.Machine.SpinlockImageProofs

namespace MachCSL.Machine.SpinlockWitness
open _root_.Sail.ConcurrencyInterfaceV1.Free
attribute [local instance] platform
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem setup00 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 0 0) =
      some ((), setupAfter 0 1) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup01 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 0 1) =
      some ((), setupAfter 0 2) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup02 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 0 2) =
      some ((), setupAfter 0 3) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup03 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 0 3) =
      some ((), setupAfter 0 4) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup04 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 0 4) =
      some ((), setupAfter 0 5) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup05 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 0 5) =
      some ((), setupAfter 0 6) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup06 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 0 6) =
      some ((), setupAfter 0 7) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup10 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 1 0) =
      some ((), setupAfter 1 1) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup11 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 1 1) =
      some ((), setupAfter 1 2) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup12 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 1 2) =
      some ((), setupAfter 1 3) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup13 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 1 3) =
      some ((), setupAfter 1 4) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup14 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 1 4) =
      some ((), setupAfter 1 5) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup15 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 1 5) =
      some ((), setupAfter 1 6) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem setup16 :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter 1 6) =
      some ((), setupAfter 1 7) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem setup_step (cpu : Fin 2) (i : Fin 7) :
    fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter cpu i.val) =
      some ((), setupAfter cpu (i.val + 1)) := by
  obtain ⟨cpu, bound⟩ := cpu
  have cases : cpu = 0 ∨ cpu = 1 := by omega
  rcases cases with rfl | rfl
  all_goals
    obtain ⟨i, hi⟩ := i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact setup00
  · exact setup01
  · exact setup02
  · exact setup03
  · exact setup04
  · exact setup05
  · exact setup06
  · exact setup10
  · exact setup11
  · exact setup12
  · exact setup13
  · exact setup14
  · exact setup15
  · exact setup16

theorem setupRun_all (cpu : Fin 2) (n : Nat) (bound : n ≤ 7) :
    setupRun cpu n = some (setupAfter cpu n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have earlier := ih (by omega)
    have next := setup_step cpu ⟨n, by omega⟩
    change (do
      let rs ← setupRun cpu n
      let (_, after) ← fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) rs
      pure after) = _
    rw [earlier]
    change (fetchRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupAfter cpu n) >>=
      fun (_, after) => some after) = _
    rw [next]
    rfl

theorem setupRun_eq (cpu : Fin 2) : setupRun cpu 7 = some (setupRegisters cpu) :=
  setupRun_all cpu 7 (by decide)

theorem setup_succeeds (cpu : Fin 2) : (setupRun cpu 7).isSome = true := by
  rw [setupRun_eq]
  rfl

private theorem boundary0 :
    ((prefixResult 0).bind fun (program, _) => (readFour program).map Prod.fst) =
      some (SpinlockAccess.readRequest .lock true) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem boundary1 :
    ((prefixResult 1).bind fun (program, _) => (readFour program).map Prod.fst) =
      some (SpinlockAccess.readRequest .lock true) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

/-- The computed pause is an actual four-byte acquire read of the lock, with
 every request field checked, rather than merely a successful evaluator stop. -/
theorem boundary_observation (cpu : Fin 2) :
    ((prefixResult cpu).bind fun (program, _) => (readFour program).map Prod.fst) =
      some (SpinlockAccess.readRequest .lock true) := by
  obtain ⟨cpu, bound⟩ := cpu
  have cases : cpu = 0 ∨ cpu = 1 := by omega
  rcases cases with rfl | rfl
  · exact boundary0
  · exact boundary1

private theorem pausedRegisters0 : (prefixResult 0).map Prod.snd = some (pausedRegisters 0) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem pausedRegisters1 : (prefixResult 1).map Prod.snd = some (pausedRegisters 1) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem paused_registers (cpu : Fin 2) :
    (prefixResult cpu).map Prod.snd = some (pausedRegisters cpu) := by
  obtain ⟨cpu, bound⟩ := cpu
  have cases : cpu = 0 ∨ cpu = 1 := by omega
  rcases cases with rfl | rfl
  · exact pausedRegisters0
  · exact pausedRegisters1

theorem prefixResult_eq (cpu : Fin 2) : prefixResult cpu = some (paused cpu) := by
  have observed := boundary_observation cpu
  have registers := paused_registers cpu
  cases h : prefixResult cpu with
  | none => simp [h] at observed
  | some pair =>
    obtain ⟨program, rs⟩ := pair
    have heq : rs = pausedRegisters cpu := by
      simpa only [h, Option.map_some, Option.some.injEq] using registers
    simp only [paused, pausedProgram, h, Option.getD_some, heq]

theorem readFour_eq (cpu : Fin 2) : readFour (paused cpu).1 = some (readBoundary cpu) := by
  have observed := boundary_observation cpu
  rw [prefixResult_eq] at observed
  cases h : readFour (paused cpu).1 with
  | none => simp [h] at observed
  | some pair => simp [readBoundary, h]

theorem boundary_request (cpu : Fin 2) :
    (readBoundary cpu).1 = SpinlockAccess.readRequest .lock true := by
  have observed := boundary_observation cpu
  rw [prefixResult_eq] at observed
  simpa only [Option.bind_some, readFour_eq, Option.map_some, Option.some.injEq] using observed

theorem readFour_program (program : SailM Unit) (req : ReadRequest 4)
    (k : ReadResult 4 → SailM Unit) (h : readFour program = some (req, k)) :
    program = .impure (.readMem 4 req) k := by
  unfold readFour at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  · contradiction

theorem paused_program (cpu : Fin 2) :
    (paused cpu).1 = .impure (.readMem 4 (SpinlockAccess.readRequest .lock true))
      (readBoundary cpu).2 := by
  have exactProgram := readFour_program (paused cpu).1 (readBoundary cpu).1
    (readBoundary cpu).2 (readFour_eq cpu)
  exact exactProgram.trans (congrArg
    (fun req : ReadRequest 4 => (.impure (.readMem 4 req) (readBoundary cpu).2 : SailM Unit))
    (boundary_request cpu))

end MachCSL.Machine.SpinlockWitness
