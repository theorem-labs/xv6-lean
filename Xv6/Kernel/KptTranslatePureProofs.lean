import Xv6.Kernel.KptTranslateSpec
import Xv6.Kernel.TlbCoherenceLink
import Xv6.Kernel.PtTreeLink
import Xv6.Kernel.KptLeafWordProofs

namespace Xv6.Kernel.KptTranslate
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem program_factor asid tree vpn access mxr doSum :
    program asid tree vpn access mxr doSum =
      lookup_TLB 39 asid vpn >>= dispatch asid tree vpn access mxr doSum := rfl

/-- Bounds and optional access follow the actual lookup's selected vector
slot, independently of coherent provenance. -/
theorem lookup_resident tlb asid vpn idx ent
    (found : TlbCoherence.lookupValue tlb asid vpn = some (idx, ent)) :
    idx = TlbCoherence.index vpn ∧ tlb[idx]? = some (some ent) := by
  unfold TlbCoherence.lookupValue at found
  split at found
  · contradiction
  · rename_i current selected
    split at found
    · have pair := Option.some.inj found
      cases pair
      refine ⟨rfl, ?_⟩
      rw [Vector.getElem?_eq_getElem (Sv39Tlb.index_bound vpn)]
      simpa only [getElem!_pos tlb (TlbCoherence.index vpn) (Sv39Tlb.index_bound vpn)]
        using congrArg some selected
    · contradiction

theorem lookup_mapped asid tree tlb vpn p2 p1 ppn permission referenceA referenceD idx ent
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD))
    (coherent : TlbCoherence.Coherent asid tree tlb)
    (found : TlbCoherence.lookupValue tlb asid vpn = some (idx, ent)) :
    idx = TlbCoherence.index vpn ∧ tlb[idx]? = some (some ent) ∧
      ∃ cachedA cachedD,
        ent = TlbCoherence.entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD) := by
  obtain ⟨indexEq, resident⟩ := lookup_resident tlb asid vpn idx ent found
  obtain ⟨_, q2, q1, q0, a, d, mapped', entryEq⟩ :=
    TlbCoherence.nativeSpec.lookup_hit asid tree tlb vpn asid idx ent coherent found
  obtain ⟨rfl, rfl, rfl⟩ := PtTree.nativeSpec.maps_det tree vpn q2 q1 q0 p2 p1
    (KptLeaf.word ppn permission referenceA referenceD) mapped' mapped
  refine ⟨indexEq, resident, a == 1#1, d == 1#1, ?_⟩
  have bitEq (bit : BitVec 1) : bit = (if bit == 1#1 then 1#1 else 0#1) := by
    have bound := bit.isLt
    have cases : bit.toNat = 0 ∨ bit.toNat = 1 := by omega
    rcases cases with zero | one
    · have same : bit = 0#1 := BitVec.eq_of_toNat_eq zero
      subst bit
      rfl
    · have same : bit = 1#1 := BitVec.eq_of_toNat_eq one
      subst bit
      rfl
  have aEq := bitEq a
  have dEq := bitEq d
  rw [aEq, dEq, KptLeaf.word_setAD] at entryEq
  exact entryEq

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM A} {Q : A → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

theorem lookup_plan shares rs asid vpn :
    RegisterPlan.Returns (footprint shares) rs (lookup_TLB 39 asid vpn)
      (TlbCoherence.lookupValue (rs .tlb) asid vpn) rs := by
  apply widen (TlbCoherence.nativePlanSpec.lookup rs asid vpn)
  intro cell member
  simp only [Sv39Tlb.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  subst cell
  simp [footprint, KptMiss.footprint]

end Xv6.Kernel.KptTranslate
