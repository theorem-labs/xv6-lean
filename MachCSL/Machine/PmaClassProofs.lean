import MachCSL.Machine.PmaClassSpec

namespace MachCSL.Machine.PmaClass
open LeanPaperStock.Functions

theorem ram_match (a : BitVec 64) (n : Nat) (range : access .ram a n) :
    matching_pma_region pmaBoot (.Physaddr a) n = some ramRegion := by
  rcases range with ⟨positive, width, lower, upper⟩
  simp only [ramLow, ramHigh] at lower upper
  have an := a.isLt
  have nn : n < 2^64 := by omega
  simp [matching_pma_region, matching_pma_region_bits_range, pmaBoot, ramRegion,
    range_subset, zopz0zIzJ_u, _root_.Sail.BitVec.toNatInt, ramLow, ramHigh,
    zero_extend, bits_of_physaddr, to_bits, _root_.Sail.BitVec.zeroExtend, _root_.Sail.get_slice_int,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.mod_eq_of_lt nn]
  all_goals repeat first | rfl | split | omega

theorem io_match (a : BitVec 64) (n : Nat) (range : access .io a n) :
    matching_pma_region pmaBoot (.Physaddr a) n = some ioRegion := by
  rcases range with ⟨positive, width, lower, upper⟩
  have an := a.isLt
  have nn : n < 2^64 := by omega
  simp [matching_pma_region, matching_pma_region_bits_range, pmaBoot, ioRegion,
    range_subset, zopz0zIzJ_u, _root_.Sail.BitVec.toNatInt, ramLow, ramHigh,
    zero_extend, bits_of_physaddr, to_bits, _root_.Sail.BitVec.zeroExtend, _root_.Sail.get_slice_int,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.mod_eq_of_lt nn]
  all_goals repeat first | rfl | split | omega

theorem ram_grants : grants .ram ramRegion := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, by intro impossible; cases impossible⟩
  intro op width bound
  simp [ramRegion, pmaBootRam, override_PMA, pma_allows_atomic_op, bound]

theorem io_grants : grants .io ioRegion := ⟨rfl, rfl⟩

theorem boot : allowsAll pmaBoot := by
  intro class_ address width admitted
  cases class_ with
  | ram => exact ⟨ramRegion, ram_match address width admitted, ram_grants⟩
  | io => exact ⟨ioRegion, io_match address width admitted, io_grants⟩

theorem ram (regions : List PMA_Region) (all : allowsAll regions) : allowsClass .ram regions := all .ram
theorem io (regions : List PMA_Region) (all : allowsAll regions) : allowsClass .io regions := all .io

theorem actual : Spec where
  ram_match := ram_match
  io_match := io_match
  ram_grants := ram_grants
  io_grants := io_grants
  boot := boot
  ram := ram
  io := io

end MachCSL.Machine.PmaClass
