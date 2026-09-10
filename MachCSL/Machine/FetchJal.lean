import MachCSL.Machine.FetchRun
import MachCSL.Machine.ColdBoot
import MachCSL.Machine.Image
import Lean.Util.CollectAxioms

/-!
Fetched execution of JAL x0,0 through the actual generated `try_step`, starting
with the register file produced by the actual generated reset/boot program.
The remainder of the loaded RAM image is zero, as specified by this small image.

Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
namespace MachCSL.Machine

open LeanPaperStock.Functions

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def jalImage : BootImage where
  vector := 0x80000000#64
  byte address := if address = 0x80000000 then 0x6f#8 else 0#8

def fetchedJalResult [Platform] : Option (Bool × RegisterFile) :=
  fetchRun (loadedRam jalImage) 2000 (try_step 0 false) (bootRegisters jalImage.vector 0#64)

/-- Actual fetch/decode/execute and step postlude, without a clock tick. -/
theorem fetchedJal_observation [Platform] :
    fetchedJalResult.map (fun (waiting, registers) =>
      (waiting, registers .PC, registers .nextPC, registers .minstret)) =
        some (false, 0x80000000#64, 0x80000000#64, 1#64) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem fetchedJal_succeeds [Platform] : fetchedJalResult.isSome = true := by
  have h := fetchedJal_observation
  cases hr : fetchedJalResult with
  | none => simp [hr] at h
  | some result => rfl

def fetchedJalRegisters [Platform] : RegisterFile :=
  (fetchedJalResult.get fetchedJal_succeeds).2

theorem fetchedJalResult_eq [Platform] : fetchedJalResult = some (false, fetchedJalRegisters) := by
  have h := fetchedJal_observation
  cases hr : fetchedJalResult with
  | none => simp [hr] at h
  | some result =>
    obtain ⟨waiting, registers⟩ := result
    have hw : waiting = false := by simpa [hr] using congrArg (Option.map Prod.fst) h
    simp [fetchedJalRegisters, hr, hw]

theorem fetchedJal_registers [Platform] :
    fetchedJalRegisters .PC = jalImage.vector ∧ fetchedJalRegisters .nextPC = jalImage.vector ∧
      fetchedJalRegisters .minstret = 1#64 := by
  have h := fetchedJal_observation
  rw [fetchedJalResult_eq] at h
  simpa [jalImage] using h

/-- The actual generated cycle consists of try_step followed by no clock tick. -/
theorem fetchedJal_cycle_result [Platform] :
    fetchRun (loadedRam jalImage) 2000 (cycle false) (bootRegisters jalImage.vector 0#64) =
      some ((), fetchedJalRegisters) := by
  change fetchRun (loadedRam jalImage) 2000
      (try_step 0 false >>= fun _ => pure ()) (bootRegisters jalImage.vector 0#64) = _
  rw [fetchRun_bind_pure]
  change fetchedJalResult.map (fun (_, rs) => ((), rs)) = _
  rw [fetchedJalResult_eq]
  rfl

def jalLocalState (devices : Device) : LocalState Device where
  registers := bootRegisters jalImage.vector 0#64
  memory := loadedRam jalImage
  devices := devices
  log := []
  view := 0
  reservation := none

/-- A finite sequence of real sub-instruction steps fetches and retires the JAL.
This is a hart-local witness; machine initialization, external-agent scheduling
and adequacy are separate obligations. The bus and reservation predicates remain
arbitrary parameters, and no assumptions about instruction correctness are used. -/
theorem fetchedJal_node_steps [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (devices : Device) :
    NodeSteps bus others 0 (loadedRam jalImage) (cycle false) (jalLocalState devices)
      (.pure ()) { jalLocalState devices with registers := fetchedJalRegisters } := by
  apply fetchRun_sound bus others 0 (loadedRam jalImage) (loadedRam jalImage) 2000
    (cycle false) (jalLocalState devices) fetchedJalRegisters ()
  · exact Nat.le_refl 0
  · intro a
    rfl
  · exact fetchedJal_cycle_result

end MachCSL.Machine

open Lean Elab Command in
run_cmd do
  for name in #[``MachCSL.Machine.fetchRun_bind_pure, ``MachCSL.Machine.fetchRun_sound,
      ``MachCSL.Machine.empty_log_read, ``MachCSL.Machine.fetchedJal_observation,
      ``MachCSL.Machine.fetchedJal_succeeds, ``MachCSL.Machine.fetchedJalResult_eq,
      ``MachCSL.Machine.fetchedJal_registers, ``MachCSL.Machine.fetchedJal_cycle_result,
      ``MachCSL.Machine.fetchedJal_node_steps] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unapproved axiom {axiomName} in {name}"
