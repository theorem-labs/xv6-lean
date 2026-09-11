import MachCSL.Machine.SupervisorPmpDefs

namespace MachCSL.Machine.SupervisorPmp
open LeanPaperStock.Functions

theorem range_match (begin finish address width : Nat)
    (low : begin ≤ address) (positive : 0 < width)
    (fits : address + width ≤ finish) :
    pmpRangeMatch begin finish address width = .PMP_Match := by
  simp only [pmpRangeMatch, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true]
  split
  · omega
  · rw [if_pos (by constructor <;> omega)]

theorem unsigned_positive (upper : BitVec 64) :
    zopz0zKzJ_u (0#64) upper = false ↔ 0 < upper.toNat := by
  simp [zopz0zKzJ_u, _root_.Sail.BitVec.toNatInt]
  omega

theorem width_bound (address : BitVec 64) (width : Nat)
    (fits : address.toNat + width ≤ ramHigh) : width < 2^64 := by
  unfold ramHigh at fits
  omega

theorem width_unsigned (width : Nat) (bound : width < 2^64) :
    (to_bits (l := 64) width).toNat = width := by
  simp [to_bits, _root_.Sail.get_slice_int]
  omega

theorem ram_range (rs : RegisterFile) (config : TorRam rs)
    (address : BitVec 64) (width : Nat) (positive : 0 < width)
    (fits : address.toNat + width ≤ ramHigh) :
    pmpRangeMatch 0 ((upper0 rs).toNat * 4) address.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match := by
  rw [width_unsigned width (width_bound address width fits)]
  exact range_match _ _ _ _ (Nat.zero_le _) positive (Nat.le_trans fits config.covers)

end MachCSL.Machine.SupervisorPmp
