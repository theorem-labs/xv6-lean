import Xv6.Kernel.KptFetchPlanDefs
import Xv6.Kernel.KptFetchHalfPureProofs

namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

set_option maxRecDepth 10000

theorem program_factor : program = factor KptFetchHalf.program := rfl

theorem unique shares : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique,footprint,KptFetchHalf.footprint,KptAddress.auxiliaryFootprint]

theorem next_two pc (aligned : is_aligned_vaddr (.Virtaddr pc) 2 = true) :
    is_aligned_vaddr (.Virtaddr (addressAdd pc 2)) 2 = true := by
  rw [KptFetchHalf.aligned_iff] at *
  simp only [addressAdd,BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

theorem low_cast (word : BitVec 32) : Sail.BitVec.extractLsb word 15 0 = KernelTextDatum.lowHalf word := rfl

theorem halves (word : BitVec 32) : BitVec.append (KernelTextDatum.highHalf word) (KernelTextDatum.lowHalf word) = word := by
  apply BitVec.eq_of_toNat_eq
  change (KernelTextDatum.highHalf word).toNat <<< 16 ||| (KernelTextDatum.lowHalf word).toNat = word.toNat
  rw [← Nat.shiftLeft_add_eq_or_of_lt (KernelTextDatum.lowHalf word).isLt]
  simp only [KernelTextDatum.highHalf,KernelTextDatum.lowHalf,BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq,Nat.reducePow,Nat.div_one]
  have bound := word.isLt
  omega

theorem bit0 pc (aligned : is_aligned_vaddr (.Virtaddr pc) 2 = true) :
    Sail.BitVec.access pc 0 = 0#1 := by
  have h := (KptFetchHalf.aligned_iff pc 2).mp aligned
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.access,BitVec.getElem_eq_testBit_toNat,Nat.testBit_zero,h]

theorem add_two (pc : BitVec 64) : Sail.BitVec.addInt pc 2 = addressAdd pc 2 := rfl

theorem nativePureSpec : PureSpec := ⟨program_factor,unique,next_two,low_cast,halves⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance instrBytes_persistent era tier pc result : Persistent (instrBytes capacity era tier pc result) := by
  unfold instrBytes
  cases result <;> simp only
  all_goals first | infer_instance | split <;> infer_instance

instance instrBytes_timeless era tier pc result : Timeless (instrBytes capacity era tier pc result) := by
  unfold instrBytes
  cases result <;> simp only
  all_goals first | infer_instance | split <;> infer_instance

instance chunkWindows_persistent era tier parts : Persistent (chunkWindows capacity era tier parts) := by
  unfold chunkWindows
  infer_instance

theorem partition era cpu rs shares :
    iprop(cells capacity era cpu rs shares ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs
        [(.PC,shares.pc),(.misa,shares.misa)] ∗
      KptFetchHalf.cells capacity era cpu rs shares.translation) :=
  RegisterFootprint.cells_append capacity.machine.era.registers (era.registers cpu) rs _ _

theorem nativeResourceSpec : ResourceSpec capacity :=
  ⟨instrBytes_persistent capacity,instrBytes_timeless capacity,partition capacity⟩

end Xv6.Kernel.KptFetch
