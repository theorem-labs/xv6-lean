import MachCSL.Devices.Plic.Proofs

/-! Source `PlicPlan.v:41–65,117–124`: every Nat context and enable word,
including out-of-range contexts, retains the source mask test. Both source integer operands are nonnegative,
so bitwise masking is represented by Nat on unsigned word values. -/
namespace MachCSL.Devices.Plic

def deviceIrqMask : Nat := (1 <<< uartIrqId) ||| (1 <<< virtioIrqId)
def deviceIrqWord (word : Nat) : Nat := if word = 0 then deviceIrqMask else 0
def enableWordOK (index : Nat) (word : Word) : Prop :=
  word.toNat &&& deviceIrqWord index = word.toNat
def PlicPlanOK (plic : State) : Prop := ∀ context word : Nat, enableWordOK word (plic.enable context word)

theorem enableWordOK_zero (index : Nat) : enableWordOK index 0 := by
  simp [enableWordOK]
theorem initial_plan : PlicPlanOK initial := by
  intro context word
  exact enableWordOK_zero word

theorem latch_plan (p p' : State) (source : Nat) (step : latch p source = some p')
    (ok : PlicPlanOK p) : PlicPlanOK p' := by
  unfold latch at step
  split at step
  · cases Option.some.inj step
    exact ok
  · cases step

end MachCSL.Devices.Plic
