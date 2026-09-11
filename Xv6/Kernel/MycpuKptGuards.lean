import Xv6.Kernel.MycpuKptCycleLink

namespace Xv6.Kernel.MycpuKpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors}

/-- Introduces every native fetch branch, without selecting a view or A/D result. -/
theorem fetch_guard_intro rs root address (next : KptFetchHalf.Step → IProp GF) :
    iprop(⊢ (∀ step, next step) -∗ KptFetchHalf.guard rs root address next) := by
  iintro Hnext
  iunfold KptFetchHalf.guard
  iintro %ppn %data %tree %p2 %p1 %a %d %path
  isplit
  · iintro %ca %cd %update
    cases update <;> simp only [KptAD.guarded]
    all_goals first | iintro !> !> | iintro !> | skip
    all_goals iintro %facts !> %view; iapply Hnext
  · iintro !> !> !> %ca %cd %v2 %v1 %v0 %update
    cases update <;> simp only [KptAD.guarded]
    all_goals first | iintro !> !> | iintro !> | skip
    all_goals iintro %facts !> %view; iapply Hnext

theorem fetch_guards_intro rs root addresses (next : List KptFetchHalf.Step → IProp GF) :
    iprop(⊢ (∀ trace, next trace) -∗ KptFetch.guardChunks rs root addresses next) := by
  induction addresses generalizing next with
  | nil =>
    simp only [KptFetch.guardChunks, List.foldr_nil]
    iintro Hnext
    iapply Hnext
  | cons address rest ih =>
    rw [KptFetch.guardChunks_cons]
    iintro Hnext
    iapply fetch_guard_intro
    iintro %step
    iapply ih
    iintro %trace
    iapply Hnext

theorem body_guards_intro r control cpu values root sp (next : MycpuKptBody.Outcome r → IProp GF) :
    iprop(⊢ (∀ outcome, next outcome) -∗ MycpuKptCycle.bodyGuards r control cpu values root sp next) := by
  cases r with
  | registers instruction =>
    simp only [MycpuKptCycle.bodyGuards]
    iintro Hnext
    iapply Hnext
  | memory kind slot =>
    iintro Hnext
    iunfold MycpuKptCycle.bodyGuards
    unfold MycpuKptMemory.guards
    iintro %ppn %data %tree %p2 %p1 %a %d
    isplit
    · iintro %ca %cd %update
      cases update <;> simp only [KptAD.guarded]
      all_goals first | iintro !> !> | iintro !> | skip
      all_goals iintro %facts !> %view; iapply Hnext
    · iintro !> !> !> %ca %cd %v2 %v1 %v0 %update
      cases update <;> simp only [KptAD.guarded]
      all_goals first | iintro !> !> | iintro !> | skip
      all_goals iintro %facts !> %view; iapply Hnext

theorem guards_intro i control cpu values root sp
    (next : List KptFetchHalf.Step → MycpuKptCycle.Outcome i → IProp GF) :
    iprop(⊢ (∀ trace outcome, next trace outcome) -∗ MycpuKptCycle.guards i control cpu values root sp next) := by
  iintro Hnext
  iunfold MycpuKptCycle.guards
  iapply fetch_guards_intro
  iintro %trace
  iapply body_guards_intro
  iintro %outcome
  iapply Hnext

end Xv6.Kernel.MycpuKpt
