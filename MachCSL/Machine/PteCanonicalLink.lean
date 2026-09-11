import MachCSL.Machine.PteCanonicalProofs

namespace MachCSL.Machine.PteCanonical
open LeanPaperStock.Functions

theorem nativeSpec : Spec := actual

theorem ppn_unchanged (w : BitVec 64) (a d : BitVec 1) :
    _root_.Sail.BitVec.extractLsb (setAD w a d) 53 10 =
      _root_.Sail.BitVec.extractLsb w 53 10 :=
  extract_unchanged w a d 10 53 (by decide) (by decide) (Or.inr (by decide))

theorem extension_unchanged (w : BitVec 64) (a d : BitVec 1) :
    _root_.Sail.BitVec.extractLsb (setAD w a d) 63 54 =
      _root_.Sail.BitVec.extractLsb w 63 54 :=
  extract_unchanged w a d 54 63 (by decide) (by decide) (Or.inr (by decide))

theorem low_flags_unchanged (w : BitVec 64) (a d : BitVec 1) :
    _root_.Sail.BitVec.extractLsb (setAD w a d) 5 0 =
      _root_.Sail.BitVec.extractLsb w 5 0 :=
  extract_unchanged w a d 0 5 (by decide) (by decide) (Or.inl (by decide))

theorem writeback_canonical (w w' : BitVec 64)
    (access : MemoryAccessType mem_payload)
    (h : LeanPaperStock.Functions.update_PTE_Bits w access = some w') : canon w' = canon w := by
  obtain ⟨a, d, rfl⟩ := update_variant w w' access h
  exact canon_variant w a d

end MachCSL.Machine.PteCanonical
