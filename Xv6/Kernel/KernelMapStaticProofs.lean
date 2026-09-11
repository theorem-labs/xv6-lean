import Xv6.Kernel.KernelMapStaticPureProofs
import MachCSL.Logic.KptGhostLink

namespace Xv6.Kernel.KernelMapStatic
open Iris Iris.BI MachCSL.Machine MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance claims_persistent γ : Persistent (claims capacity γ) := by
  unfold claims
  infer_instance

instance authority_timeless γ : Timeless (authority capacity γ) := by
  unfold authority
  infer_instance

theorem allocate (frame : IProp GF) : iprop(frame ⊢ |==> ∃ γ,
    authority capacity γ ∗ claims capacity γ ∗ frame) :=
  (KptGhost.nativeSpec capacity.ghost).allocateMap initialMap frame

theorem claim_lookup γ vpn permission (given : Static vpn permission) :
    iprop(claims capacity γ ⊢ KptGhost.mapAt capacity.ghost γ vpn (identityPPN vpn) permission) := by
  apply (KptGhost.nativeSpec capacity.ghost).claimLookup
  rw [lookup, given]
  rfl

theorem identify γ vpn ppn permission :
    iprop(⊢ authority capacity γ -∗ KptGhost.mapAt capacity.ghost γ vpn ppn permission -∗
      ⌜Static vpn permission ∧ ppn = identityPPN vpn⌝) := by
  iintro Hauth Hclaim
  ihave %found := (KptGhost.nativeSpec capacity.ghost).mapLookup γ initialMap vpn ppn permission
    $$ [Hauth Hclaim]
  · iunfold authority at Hauth
    iframe Hauth Hclaim
  ipureintro
  rw [lookup] at found
  cases classified : classify vpn with
  | none => simp [classified] at found
  | some actual =>
    simp only [classified, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
    exact ⟨by unfold Static; rw [classified, found.2], found.1.symm⟩

theorem actual : Spec capacity :=
  ⟨claims_persistent capacity, authority_timeless capacity, allocate capacity,
    claim_lookup capacity, identify capacity⟩

end Xv6.Kernel.KernelMapStatic
