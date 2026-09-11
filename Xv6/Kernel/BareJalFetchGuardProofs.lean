import Xv6.Kernel.BareJalFetchChunkProofs

namespace Xv6.Kernel.BareJalFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem guard_fold_prefix {GF : BundledGFunctors} addresses (done : List Nat → IProp GF) prior :
    addresses.foldr (fun (_ : BitVec 64) next views => iprop(▷ ∀ view : Nat, next (views ++ [view]))) done prior =
      guardReads addresses (fun views => done (prior ++ views)) := by
  unfold guardReads
  have aux : ∀ (addresses : List (BitVec 64)) (prior suffix : List Nat),
      addresses.foldr (fun _ next views => iprop(▷ ∀ view : Nat, next (views ++ [view]))) done (prior ++ suffix) =
      addresses.foldr (fun _ next views => iprop(▷ ∀ view : Nat, next (views ++ [view])))
        (fun views => done (prior ++ views)) suffix := by
    intro addresses
    induction addresses with
    | nil => intros; rfl
    | cons address rest ih =>
      intro prior suffix
      simp only [List.foldr_cons]
      congr 2
      funext view
      rw [List.append_assoc]
      exact ih prior (suffix ++ [view])
  simpa only [List.append_nil] using aux addresses prior []

theorem guardReads_cons {GF : BundledGFunctors} address addresses (done : List Nat → IProp GF) :
    guardReads (address :: addresses) done =
      iprop(▷ ∀ view : Nat, guardReads addresses (fun views => done (view :: views))) := by
  unfold guardReads
  simp only [List.foldr_cons,List.nil_append]
  congr 2
  funext view
  exact guard_fold_prefix addresses done [view]

variable {GF : BundledGFunctors}

theorem guardReads_mono addresses (left right : List Nat → IProp GF) :
    iprop(⊢ (∀ views, left views -∗ right views) -∗ guardReads addresses left -∗ guardReads addresses right) := by
  induction addresses generalizing left right with
  | nil =>
    simp only [guardReads,List.foldr_nil]
    iintro Hmap Hguard
    iapply Hmap $$ %([]) Hguard
  | cons address rest ih =>
    rw [guardReads_cons,guardReads_cons]
    iintro Hmap Hguard
    iintro !> %view
    ihave Hguard := Hguard $$ %view
    iapply ih $$ [Hmap] Hguard
    iintro %views Hleft
    iapply Hmap $$ %(view :: views) Hleft

theorem guards_mono pc (left right : List Nat → IProp GF) :
    iprop(⊢ (∀ views, left views -∗ right views) -∗ guards pc left -∗ guards pc right) :=
  guardReads_mono _ left right

end Xv6.Kernel.BareJalFetch
