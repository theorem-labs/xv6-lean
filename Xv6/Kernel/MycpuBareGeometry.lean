import Xv6.Kernel.MycpuBareDefs
import MachCSL.Logic.TsoContextWordProofs
import MachCSL.Logic.TsoOwnership
import MachCSL.Logic.StackPhysicalProofs
import Xv6.Kernel.MycpuCycleBodyPlan

namespace Xv6.Kernel.MycpuBare
open Iris Iris.BI MachCSL.Memory MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

def ramRegion : PMA_Region :=
  ⟨BitVec.ofNat 64 ramLow, BitVec.ofNat 64 (ramHigh - ramLow), pmaBootRam, true⟩

theorem aligned_ram_range (a : PhysicalAddress) (aligned : TsoContextWord.Aligned a)
    (ram : Tso.AddrIsRAM a) : SupervisorPhysical.RamRange a 8 := by
  unfold TsoContextWord.Aligned at aligned
  unfold Tso.AddrIsRAM at ram
  unfold SupervisorPhysical.RamRange ramLow ramHigh
  omega

theorem word_range {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) ξ a dq word :
    iprop(⊢ TsoContextReadWP.wordPointsto capacity era ξ a dq word -∗
      ⌜SupervisorPhysical.RamRange a 8⌝) := by
  unfold TsoContextReadWP.wordPointsto TsoContextWord.pointsto
  iintro ⟨%aligned, Hbytes⟩
  have first : (List.range 8)[0]? = some 0 := rfl
  ihave Hbyte := BigSepL.bigSepL_lookup first $$ Hbytes
  isimp only [addressAdd, BitVec.add_zero] at Hbyte
  iunfold TsoContext.physPointsto at Hbyte
  icases Hbyte with ⟨%time, Hbyte, _, _⟩
  ihave %ram := Tso.physBytePointsto_ram _ _ _ _ _ $$ Hbyte
  ipureintro
  exact aligned_ram_range a aligned ram

theorem pma_ram (a : PhysicalAddress) (n : Nat) (width : n ≤ 8)
    (range : SupervisorPhysical.RamRange a n) :
    matching_pma_region pmaBoot (.Physaddr a) n = some ramRegion := by
  rcases range with ⟨positive, lower, upper⟩
  simp only [ramLow, ramHigh] at lower upper
  have an := a.isLt
  have nn : n < 2^64 := by omega
  simp [matching_pma_region, matching_pma_region_bits_range, pmaBoot, ramRegion,
    range_subset, zopz0zIzJ_u, _root_.Sail.BitVec.toNatInt, ramLow, ramHigh,
    zero_extend, bits_of_physaddr, to_bits, _root_.Sail.BitVec.zeroExtend, _root_.Sail.get_slice_int,
    BitVec.toNat_add, BitVec.toNat_sub,
    Nat.mod_eq_of_lt nn]
  all_goals repeat first | rfl | split | omega

theorem remaining_unique (shares : FrameShares) : RegisterFootprint.Unique (frameFootprint shares) := by
  simp [RegisterFootprint.Unique, frameFootprint, remainingSaved]

theorem combined_unique (shares : Shares) (frameShares : FrameShares) :
    RegisterFootprint.Unique (MycpuCycleBody.footprint shares ++ frameFootprint frameShares) := by
  simp [RegisterFootprint.Unique, frameFootprint, remainingSaved, MycpuCycleBody.footprint,
    MycpuActive.footprint, MycpuFetch.footprint, SupervisorBareFetch.footprint,
    SupervisorBare.footprint, SupervisorFetchRead.footprint,
    SupervisorRetirement.retirementFootprint, SupervisorClock.clockFootprint]

theorem combined_length (shares : Shares) (frameShares : FrameShares) :
    (MycpuCycleBody.footprint shares ++ frameFootprint frameShares).length = 39 := rfl

end Xv6.Kernel.MycpuBare
