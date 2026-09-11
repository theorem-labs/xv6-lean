import MachCSL.Logic.SupervisorPteADDefs
import Xv6.Kernel.KptLeafWordProofs
import MachCSL.Machine.PteCanonicalProofs

namespace MachCSL.Logic.SupervisorPteAD
open MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions Xv6.Kernel

/-- Any actual generated update stays in the same canonical leaf family. -/
theorem update_canonical (ppn : BitVec 44) (permission : KptLeaf.Permission)
    (a d : Bool) (access : MemoryAccessType mem_payload) (new : BitVec 64)
    (changed : update_PTE_Bits (KptLeaf.word ppn permission a d) access = some new) :
    PteCanonical.canon new = KptLeaf.word ppn permission false false := by
  obtain ⟨a', d', rfl⟩ := PteCanonical.update_variant _ new access changed
  rw [PteCanonical.canon_variant, KptLeaf.word_canonical]

theorem canonical_members (ppn : BitVec 44) (permission : KptLeaf.Permission)
    (new : BitVec 64)
    (canonical : PteCanonical.canon new = KptLeaf.word ppn permission false false) :
    ∀ j, j < 8 → nthByte new j ∈ PteCanonical.slotSet (KptLeaf.word ppn permission false false) j := by
  have same : PteCanonical.canon new = PteCanonical.canon (KptLeaf.word ppn permission false false) := by
    rw [KptLeaf.word_canonical]; exact canonical
  obtain ⟨a, d, rfl⟩ := PteCanonical.canon_inv _ new same
  exact fun j bound => PteCanonical.slot_mem_variant _ a d j (KptLeaf.word_leaf _ _ _ _) bound

end MachCSL.Logic.SupervisorPteAD
