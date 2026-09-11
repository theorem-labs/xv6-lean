import Xv6.Kernel.PtTreeWordProofs

namespace Xv6.Kernel.PtTree
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem flags_low_setAD (w : Word) (a d : BitVec 1) (j : Nat) (hj : j < 6) :
    _root_.Sail.BitVec.extractLsb (PteCanonical.flags (PteCanonical.setAD w a d)) j j =
      _root_.Sail.BitVec.extractLsb (PteCanonical.flags w) j j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst i
  have hj8 : j < 8 := by omega
  have hj64 : j < 64 := by omega
  simp only [PteCanonical.flags, Mk_PTE_Flags, _root_.Sail.BitVec.extractLsb,
    BitVec.getLsbD_extractLsb]
  simp only [Nat.add_zero, Nat.zero_add, hj8, decide_true, Bool.true_and]
  rw [PteCanonical.setAD_bit w a d j hj64]
  simp [show j ≠ 6 by omega, show j ≠ 7 by omega]

theorem ext_setAD (w : Word) (a d : BitVec 1) :
    ext_bits_of_PTE (PteCanonical.setAD w a d) = ext_bits_of_PTE w :=
  PteCanonical.extension_unchanged w a d

theorem global_setAD (w : Word) (a d : BitVec 1) :
    globalBit (PteCanonical.setAD w a d) = globalBit w := by
  simp only [globalBit, _get_PTE_Flags_G, flags_low_setAD w a d 5 (by decide)]

theorem leaf_setAD (w : Word) (a d : BitVec 1) :
    Leaf (PteCanonical.setAD w a d) ↔ Leaf w := by
  simp only [Leaf, PteCanonical.nonleaf_variant]

theorem validation_setAD (w : Word) (a d : BitVec 1) (leaf : Leaf w) :
    validation (PteCanonical.setAD w a d) = validation w := by
  rw [validation_eq, validation_eq]
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .menvcfg >>= k)
  funext environment1
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .misa >>= k)
  funext isa1
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .misa >>= k)
  funext isa2
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .menvcfg >>= k)
  funext environment2
  apply congrArg (fun k : BitVec 64 → SailM Bool => _root_.Sail.readReg .misa >>= k)
  funext isa3
  have low := flags_low_setAD w a d
  change PteCanonical.nonleaf w = false at leaf
  have leaf' : pte_is_non_leaf (PteCanonical.flags (PteCanonical.setAD w a d)) = false :=
    (PteCanonical.nonleaf_variant w a d).trans leaf
  change pte_is_non_leaf (PteCanonical.flags w) = false at leaf
  simp only [invalidValue, ext_setAD, leaf', leaf, Bool.false_and, Bool.false_or, _get_PTE_Flags_V, _get_PTE_Flags_R,
    _get_PTE_Flags_W, _get_PTE_Flags_X, low 0 (by decide), low 1 (by decide),
    low 2 (by decide), low 3 (by decide)]

theorem set_ad_valid_leaf (w : Word) (a d : BitVec 1) (leaf : Leaf w) :
    Valid (PteCanonical.setAD w a d) ↔ Valid w := by
  simp only [Valid, Outcome, validation_setAD w a d leaf]

theorem canon_valid_leaf (w : Word) (leaf : Leaf w) :
    Valid (PteCanonical.canon w) ↔ Valid w := set_ad_valid_leaf w 0#1 0#1 leaf

theorem canon_leaf (w : Word) : Leaf (PteCanonical.canon w) ↔ Leaf w :=
  leaf_setAD w 0#1 0#1

theorem canon_napot (w : Word) : NoNapot (PteCanonical.canon w) ↔ NoNapot w := by
  simp only [NoNapot, PteCanonical.canon, ext_setAD]

theorem canon_pbmt (w : Word) : PbmtZero (PteCanonical.canon w) ↔ PbmtZero w := by
  simp only [PbmtZero, PteCanonical.canon, ext_setAD]

end Xv6.Kernel.PtTree
