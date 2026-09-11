import MachCSL.Logic.SupervisorPteADFactorDefs
import MachCSL.Logic.RegisterPlanProofs
import MachCSL.Logic.EventPlanCombinators

namespace MachCSL.Logic.SupervisorPteAD
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

/-- Factorization of the exact generated tree, retaining all error and
Boolean response branches before applying native memory rules. -/
theorem program_eq vpn address cached access mxr doSum :
    program vpn address cached access mxr doSum =
      match update_PTE_Bits cached access with
      | none => pure (.Ok (none, ()))
      | some _ => gate >>= afterGate vpn address access mxr doSum := by
  unfold afterGate afterRead afterCheck afterWrite
  simp [program, update_and_write_pte, gate,
    BitVec.setWidth_eq, BootPmp.sail_bind_assoc, BootPmp.sail_pure_bind]
  cases choice : update_PTE_Bits cached access with
  | none => rfl
  | some _ =>
    simp only [currentlyEnabled, hartSupports, BootPmp.sail_pure_bind]
    apply congrArg (fun next : BitVec 64 → SailM Result => _root_.Sail.readReg .menvcfg >>= next)
    funext environment
    split
    · apply congrArg (fun next : SupervisorPteRead.Result → SailM Result =>
        read_pte_exclusive (.Physaddr address) 8 >>= next)
      funext readResult
      cases readResult with
      | Err error => rfl
      | Ok physical =>
        apply congrArg (fun next : _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → SailM Result =>
          check_leaf_pte 39 vpn access .Supervisor mxr doSum physical (.Physaddr address) 0 () >>= next)
        funext checked
        cases checked with
        | Err error => cases error; rfl
        | Ok value =>
          rcases value with ⟨ppn, pbmt, ext⟩
          cases ext
          cases update_PTE_Bits physical access <;> rfl
    · rfl


theorem gate_eq : gate = (do
    let env ← _root_.Sail.readReg .menvcfg
    pure (_get_MEnvcfg_ADUE env == 1#1) : SailM Bool) := by
  simp only [gate, currentlyEnabled, hartSupports, BootPmp.sail_pure_bind,
    Bool.true_and, LeanPaperStock.Functions.not, Bool.not_true, Bool.false_and, Bool.or_false]

theorem gate_plan (shares : Shares) (rs : RegisterFile) :
    RegisterPlan.Returns (footprint shares) rs gate (enabled rs) rs := by
  rw [gate_eq]
  exact .read (dq := shares.environment) (by simp [footprint, SupervisorPteRead.footprint, SupervisorRead.footprint])
    (.pure ⟨rfl, rfl⟩)

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint, SupervisorPteRead.footprint, SupervisorRead.footprint]

end MachCSL.Logic.SupervisorPteAD
