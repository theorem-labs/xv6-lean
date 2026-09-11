import Xv6.Kernel.KernelTextDatumSpec

namespace Xv6.Kernel.KernelTextDatum
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic KernelDatum

theorem text_ram pa (h : AddrIsText pa) : Tso.AddrIsRAM pa := by
  unfold AddrIsText textEnd at h
  unfold Tso.AddrIsRAM
  omega

theorem text_end_symbol : (textEnd : Int) = Xv6.Generated.KernelMaps.Symbols.etext := rfl

theorem trampoline_text (j : Nat) (h : j < 4096) :
    AddrIsText (BitVec.ofInt 64 (Xv6.Generated.KernelMaps.Symbols.trampoline + j)) := by
  simp only [AddrIsText, textEnd, Xv6.Generated.KernelMaps.Symbols.trampoline,
    BitVec.toNat_ofInt]
  omega

theorem page_two va (h : va.toNat % 2 = 0) : SamePage va 2 := by
  unfold SamePage
  omega

theorem page_four va (h : va.toNat % 4 = 0) : SamePage va 4 := by
  unfold SamePage
  omega

private theorem address_add va n j (aligned : SamePage va n) (bound : j < n) :
    (addressAdd va j).toNat = va.toNat + j := by
  have size := va.isLt
  unfold SamePage at aligned
  simp only [addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem vpn_offset va n j (aligned : SamePage va n) (bound : j < n) :
    vpn (addressAdd va j) = vpn va := by
  apply BitVec.eq_of_toNat_eq
  simp only [vpn, KernelDatum.vpn, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [address_add va n j aligned bound]
  have window := aligned
  unfold SamePage at window
  omega

private theorem physical_nat va ppn :
    (physical ppn va).toNat = ppn.toNat * 4096 + va.toNat % 4096 := by
  have size := ppn.isLt
  change ((ppn ++ va.extractLsb' 0 12).setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (va.extractLsb' 0 12).isLt]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftLeft_eq]
  omega

theorem physical_offset va ppn n j (aligned : SamePage va n) (bound : j < n) :
    physical ppn (addressAdd va j) = addressAdd (physical ppn va) j := by
  apply BitVec.eq_of_toNat_eq
  rw [physical_nat, address_add va n j aligned bound]
  simp only [addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [physical_nat]
  have size := ppn.isLt
  have window := aligned
  unfold SamePage at window
  omega

theorem low_bytes (word : BitVec 32) (j : Nat) (h : j < 2) :
    nthByte (lowHalf word) j = nthByte word j := by
  apply BitVec.eq_of_toNat_eq
  simp only [nthByte, lowHalf, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with rfl | rfl <;> simp only [Nat.reduceMul, Nat.reducePow, Nat.div_one] <;> omega

theorem high_bytes (word : BitVec 32) (j : Nat) (h : j < 2) :
    nthByte (highHalf word) j = nthByte word (2 + j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [nthByte, highHalf, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with rfl | rfl <;> simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.div_one] <;> omega

theorem nativePureSpec : PureSpec :=
  ⟨text_ram,text_end_symbol,trampoline_text,page_two,page_four,vpn_offset,
    physical_offset,low_bytes,high_bytes⟩

end Xv6.Kernel.KernelTextDatum
