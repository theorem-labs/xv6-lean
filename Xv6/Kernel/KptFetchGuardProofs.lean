import Xv6.Kernel.KptFetchPlanProofs
import Xv6.Kernel.KptFetchHalfProofs

namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Moving a prior into the final trace preserves the actual modal fold. -/
theorem guard_fold_prefix {GF : BundledGFunctors} rs root addresses
    (done : List KptFetchHalf.Step → IProp GF) prior :
    addresses.foldr (fun address next trace =>
      KptFetchHalf.guard rs root address (fun step => next (trace ++ [step]))) done prior =
    guardChunks rs root addresses (fun trace => done (prior ++ trace)) := by
  unfold guardChunks
  have aux : ∀ (addresses : List (BitVec 64)) (prior suffix : List KptFetchHalf.Step),
      addresses.foldr (fun address next trace =>
        KptFetchHalf.guard rs root address (fun step => next (trace ++ [step]))) done (prior ++ suffix) =
      addresses.foldr (fun address next trace =>
        KptFetchHalf.guard rs root address (fun step => next (trace ++ [step])))
        (fun trace => done (prior ++ trace)) suffix := by
    intro addresses
    induction addresses with
    | nil => intros; rfl
    | cons address rest ih =>
      intro prior suffix
      simp only [List.foldr_cons]
      congr 1
      funext step
      rw [List.append_assoc]
      exact ih prior (suffix ++ [step])
  simpa only [List.append_nil] using aux addresses prior []

theorem guardChunks_cons {GF : BundledGFunctors} rs root address addresses
    (done : List KptFetchHalf.Step → IProp GF) :
    guardChunks rs root (address :: addresses) done =
    KptFetchHalf.guard rs root address (fun step =>
      guardChunks rs root addresses (fun trace => done (step :: trace))) := by
  unfold guardChunks
  simp only [List.foldr_cons,List.nil_append]
  congr 1
  funext step
  exact guard_fold_prefix rs root addresses done [step]

variable {GF : BundledGFunctors}

theorem guard_mono rs root address (left right : KptFetchHalf.Step → IProp GF) :
    iprop(⊢ (∀ step, left step -∗ right step) -∗
      KptFetchHalf.guard rs root address left -∗ KptFetchHalf.guard rs root address right) := by
  iintro Hmap Hguard
  iunfold KptFetchHalf.guard
  iunfold KptFetchHalf.guard at Hguard
  iintro %ppn %data %tree %p2 %p1 %a %d %path
  ihave Hguard := Hguard $$ %ppn %data %tree %p2 %p1 %a %d %path
  isplit
  · ihave Hguard := Iris.BI.and_elim_l $$ Hguard
    iintro %ca %cd %update
    ihave Hguard := Hguard $$ %ca %cd %update
    cases update <;> simp only [KptAD.guarded]
    all_goals first | iintro !> !> | iintro !> | skip
    all_goals
      iintro %facts
      ihave Hguard := Hguard $$ %facts
      iintro !> %view
      ihave Hguard := Hguard $$ %view
      iapply Hmap $$ Hguard
  · ihave Hguard := Iris.BI.and_elim_r $$ Hguard
    iintro !> !> !> %ca %cd %v2 %v1 %v0 %update
    ihave Hguard := Hguard $$ %ca %cd %v2 %v1 %v0 %update
    cases update <;> simp only [KptAD.guarded]
    all_goals first | iintro !> !> | iintro !> | skip
    all_goals
      iintro %facts
      ihave Hguard := Hguard $$ %facts
      iintro !> %view
      ihave Hguard := Hguard $$ %view
      iapply Hmap $$ Hguard

theorem guardChunks_mono rs root addresses (left right : List KptFetchHalf.Step → IProp GF) :
    iprop(⊢ (∀ trace, left trace -∗ right trace) -∗
      guardChunks rs root addresses left -∗ guardChunks rs root addresses right) := by
  induction addresses generalizing left right with
  | nil =>
    simp only [guardChunks,List.foldr_nil]
    iintro Hmap Hguard
    iapply Hmap $$ %([]) Hguard
  | cons address rest ih =>
    rw [guardChunks_cons,guardChunks_cons]
    iintro Hmap Hguard
    iapply guard_mono $$ [Hmap] Hguard
    iintro %step Hrest
    iapply ih $$ [Hmap] Hrest
    iintro %trace Hleft
    iapply Hmap $$ %(step :: trace) Hleft

end Xv6.Kernel.KptFetch
