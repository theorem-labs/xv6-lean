import Xv6.Kernel.PushOffWord4Factor
import Xv6.Kernel.PushOffWord4Resources
import Xv6.Kernel.PushOffWord4BareLink
import Xv6.Kernel.KptMemory4Link
import Xv6.Kernel.MycpuKptMemoryRules
namespace Xv6.Kernel.PushOffWord4
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem source_plan shares control cpu values :
    RegisterPlan.Returns (footprint shares) (entry control cpu values)
      (rX_bits (.Regidx 15#5)) (HartTp.rget cpu values 15#5) (entry control cpu values) :=
  .read (dq := .own 1) (by simp [footprint]) (.pure ⟨rfl,rfl⟩)
theorem base_plan shares control cpu values :
    RegisterPlan.Returns (footprint shares) (entry control cpu values)
      (rX_bits (.Regidx 10#5)) (HartTp.rget cpu values 10#5) (entry control cpu values) :=
  .read (dq := .own 1) (by simp [footprint]) (.pure ⟨rfl,rfl⟩)
theorem load_tail_plan shares control cpu values old :
    RegisterPlan.Returns (footprint shares) (entry control cpu values)
      (loadTail (.Ok old)) (.Retire_Success ())
      (entry control cpu (HartTp.set values 15#5 (old.signExtend 64))) := by
  rw [entry_load]
  exact .write (by simp [footprint]) (.pure ⟨rfl,rfl⟩)

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
theorem guards_frame regime rs op va (P Q : Outcome regime → Nat → IProp GF)
    (R : IProp GF) (next : ∀ outcome view, iprop(R ∗ P outcome view ⊢ Q outcome view)) :
    iprop(R ∗ guards regime rs op va P ⊢ guards regime rs op va Q) := by
  cases regime with
  | bare =>
    unfold guards
    iintro ⟨HR,HP⟩ !> %view
    ihave HP := HP $$ %view
    iapply next () view $$ [HR HP]; iframe
  | kpt N root =>
    unfold guards
    apply MycpuKptMemory.guards_frame
    intro ppn data outcome
    iintro ⟨HR,HP⟩ %facts
    ihave HP := HP $$ %facts
    iintro !> %view
    ihave HP := HP $$ %view
    iapply next outcome view $$ [HR HP]; iframe
end Xv6.Kernel.PushOffWord4
