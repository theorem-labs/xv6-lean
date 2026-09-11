import Xv6.Kernel.PushOffStackFactor
import Xv6.Kernel.PushOffStackResources
import Xv6.Kernel.KptMemoryLink
import MachCSL.Logic.RegisterPlanProofs

namespace Xv6.Kernel.PushOffStack
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem source_plan shares control cpu values slot :
    RegisterPlan.Returns (footprint shares slot) (entry control cpu values)
      (rX_bits (regidx slot)) (sourceValue cpu values slot) (entry control cpu values) := by
  cases slot <;> exact .read (dq := .own 1) (by simp [footprint, register]) (.pure ⟨rfl,rfl⟩)

theorem sp_plan shares control cpu values slot :
    RegisterPlan.Returns (footprint shares slot) (entry control cpu values)
      (rX_bits (.Regidx 2#5)) (HartTp.rget cpu values 2#5) (entry control cpu values) :=
  .read (dq := .own 1) (by simp [footprint]) (.pure ⟨rfl,rfl⟩)

theorem load_tail_plan shares control cpu values slot word :
    RegisterPlan.Returns (footprint shares slot) (entry control cpu values)
      (loadTail slot (.Ok word)) (.Retire_Success ())
      (entry control cpu (afterMap .load slot values word)) := by
  rw [entry_load]
  cases slot <;> exact .write (by simp [footprint, register]) (.pure ⟨rfl,rfl⟩)

namespace Kpt
variable {GF : BundledGFunctors}

theorem guards_frame (P Q : PtTree.PPN → KptAddress.Data → KptAddress.Outcome → IProp GF)
    (R : IProp GF) (next : ∀ ppn data outcome, iprop(R ∗ P ppn data outcome ⊢ Q ppn data outcome)) :
    iprop(R ∗ guards P ⊢ guards Q) := by
  unfold guards MycpuKptMemory.guards
  iintro ⟨HR,Hfinish⟩ %ppn %data %tree %p2 %p1 %ra %rd
  ihave Hfinish := Hfinish $$ %ppn %data %tree %p2 %p1 %ra %rd
  isplit
  · ihave Hfinish := Iris.BI.and_elim_l $$ Hfinish
    iintro %a %d %update
    ihave Hfinish := Hfinish $$ %a %d %update
    cases update <;> simp only [KptAD.guarded]
    all_goals first | iintro !> !> | iintro !> | skip
    all_goals iapply next ppn data _ $$ [HR Hfinish]
    all_goals iframe
  · ihave Hfinish := Iris.BI.and_elim_r $$ Hfinish
    iintro !> !> !> %a %d %v2 %v1 %v0 %update
    ihave Hfinish := Hfinish $$ %a %d %v2 %v1 %v0 %update
    cases update <;> simp only [KptAD.guarded]
    all_goals first | iintro !> !> | iintro !> | skip
    all_goals iapply next ppn data _ $$ [HR Hfinish]
    all_goals iframe

end Kpt
end Xv6.Kernel.PushOffStack
