import MachCSL.Machine.PteCanonicalDefs

namespace MachCSL.Machine.PteCanonical
open LeanPaperStock.Functions MachCSL.Memory

structure Spec : Prop where
  bit : ∀ w a d i, i < 64 → (setAD w a d).getLsbD i =
    if i = 6 then a.getLsbD 0 else if i = 7 then d.getLsbD 0 else w.getLsbD i
  absorb : ∀ w a d a' d', setAD (setAD w a d) a' d' = setAD w a' d'
  canon_variant : ∀ w a d, canon (setAD w a d) = canon w
  canon_inv : ∀ w w', canon w' = canon w → ∃ a d, w' = setAD w a d
  nonleaf_variant : ∀ w a d, nonleaf (setAD w a d) = nonleaf w
  high_byte : ∀ w a d j, 0 < j → j < 8 → nthByte (setAD w a d) j = nthByte w j
  family_variant : ∀ w a d j, Leaf w → j < 8 → slotSet (setAD w a d) j = slotSet w j
  writeback : ∀ w w' (access : MemoryAccessType mem_payload),
    update_PTE_Bits w access = some w' → Leaf w → WritebackOK w w'
  exact_nonleaf : ∀ w w', nonleaf w = true →
    (∀ j, j < 8 → nthByte w' j ∈ slotSet w j) → w' = w
  canonical_read : ∀ w w',
    (∀ j, j < 8 → nthByte w' j ∈ slotSet w j) → canon w' = canon w
  family_read : ∀ w w', Leaf w →
    (∀ j, j < 8 → nthByte w' j ∈ slotSet w j) →
    ∀ j, j < 8 → slotSet w' j = slotSet w j

end MachCSL.Machine.PteCanonical
