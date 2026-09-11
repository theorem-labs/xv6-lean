import Xv6.Kernel.Sv39TreeWalkSpec
import Xv6.Kernel.PtTreeLink
import Xv6.Kernel.Sv39WalkFactor

namespace Xv6.Kernel.Sv39TreeWalk
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem address_same (ppn : PtTree.PPN) (level : Nat) (vpn : PtTree.VPN) :
    Sv39Walk.addressAt ppn (Sv39Walk.index vpn level) =
      PtTree.slotAddress ppn (PtTree.index level vpn) := by
  rcases level with _ | level
  · rfl
  rcases level with _ | level
  · rfl
  rcases level with _ | level <;> rfl

/-- The actual recursive branch preserves the entire raw PPN and G bit. -/
theorem pointer_next (vpn : PtTree.VPN) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) (raw : PtTree.Word) (pointer : PtTree.Pointer raw)
    (address : physaddr) (level : Nat) (positive : 0 < level) (global : Bool) :
    Sv39Walk.afterInvalid vpn access mxr doSum raw address level global false =
      pt_walk 39 vpn access .Supervisor mxr doSum (PtTree.nextBase raw) (level - 1)
        (global || PtTree.globalBit raw) () := by
  unfold Sv39Walk.afterInvalid
  have nonleaf : pte_is_non_leaf (PteCanonical.flags raw) = true := pointer
  have pos : (level >b 0) = true := decide_eq_true positive
  simp only [LeanPaperStock.Functions.not, Bool.not_false, nonleaf, pos,
    Bool.true_and, ↓reduceIte]
  rfl

theorem leaf_global (ppn : PtTree.PPN) (permission : KptLeaf.Permission) (a d : Bool) :
    PtTree.globalBit (KptLeaf.word ppn permission a d) = false := by
  unfold PtTree.globalBit
  rw [KptLeaf.word_flags]
  cases permission <;> cases a <;> cases d <;> rfl

theorem output_eq (tree : PtTree.Tree) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word)
    (ppn : PtTree.PPN) (permission : KptLeaf.Permission) (global a d : Bool) :
    Sv39Walk.output (geometry tree p2 p1 ppn) vpn permission
      ((global || PtTree.globalBit p2) || PtTree.globalBit p1) a d =
    output vpn p2 p1 ppn permission global a d := by
  unfold output PtTree.globalAfter
  rw [leaf_global, Bool.or_false]
  rfl

theorem mapped_pointers tree vpn p2 p1 p0 (mapped : PtTree.Maps tree vpn p2 p1 p0) :
    PtTree.Valid p2 ∧ PtTree.Pointer p2 ∧ PtTree.Valid p1 ∧ PtTree.Pointer p1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, v2, ptr2, v1, ptr1, _⟩ := mapped
  exact ⟨v2, ptr2, v1, ptr1⟩

end Xv6.Kernel.Sv39TreeWalk
