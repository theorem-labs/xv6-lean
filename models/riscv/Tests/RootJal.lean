import LeanPaperStock.InstsEnd
import Lean.Util.CollectAxioms

open Sail LeanPaperStock.Functions
open Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace RootJal
variable [Platform]

abbrev Registers := (r : Register) → RegisterType r
abbrev Observation := (event : Event RegisterType exception) × event.Result

def defaultRegisters (r : Register) : RegisterType r := by
  cases r <;> exact default

def update (registers : Registers) (r : Register) (value : RegisterType r) : Registers :=
  fun q => if h : r = q then h ▸ value else registers q

/-- A fixture for this instruction experiment, not a proved machine boot state. -/
def registerFixture : Registers :=
  update (update (update defaultRegisters .PC 0x80000000#64)
    .nextPC 0x80000004#64) .misa 0x800000000014112d#64

def run {α : Type} : Nat → SailM α → Registers → Option (α × Registers × List Observation)
  | 0, _, _ => none
  | _ + 1, .pure value, registers => some (value, registers, [])
  | fuel + 1, .impure event continuation, registers =>
    match event with
    | .readReg r => do
      let result := registers r
      let (value, after, rest) ← run fuel (continuation result) registers
      pure (value, after, ⟨.readReg r, result⟩ :: rest)
    | .writeReg r result => do
      let (value, after, rest) ← run fuel (continuation ()) (update registers r result)
      pure (value, after, ⟨.writeReg r result, ()⟩ :: rest)
    | _ => none

/-- Kernel-checked execution of the actual generated JAL body under the stated
register-only interpreter. No fetch, initialization, concurrency or adequacy claim. -/
theorem execute_jal_trace :
    (run 30 (execute (.JAL (0#21, .Regidx 0#5))) registerFixture).map
      (fun result => (result.1, result.2.2)) =
    some (ExecutionResult.Retire_Success (), [
      ⟨.readReg .nextPC, 0x80000004#64⟩,
      ⟨.readReg .PC, 0x80000000#64⟩,
      ⟨.readReg .misa, 0x800000000014112d#64⟩,
      ⟨.writeReg .nextPC 0x80000000#64, ()⟩]) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem execute_jal_nextPC :
    (run 30 (execute (.JAL (0#21, .Regidx 0#5))) registerFixture).map
      (fun result => result.2.1 .nextPC) = some 0x80000000#64 := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

#print axioms execute_jal_trace
#print axioms execute_jal_nextPC
end RootJal

open Lean Elab Command in
run_cmd do
  for name in #[``RootJal.execute_jal_trace, ``RootJal.execute_jal_nextPC] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unapproved axiom {axiomName} in {name}"

/- Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account. -/
