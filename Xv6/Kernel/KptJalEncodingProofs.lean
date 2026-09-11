import Xv6.Kernel.KptJalSpec
import Xv6.Kernel.KptFetchPureProofs

namespace Xv6.Kernel.KptJal
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem access_extract {w : Nat} (x : BitVec w) (i : Nat) (bound : i < w) :
    Sail.BitVec.access x i = x.extractLsb' i 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have eq : j = 0 := by omega
  subst j
  simp only [Sail.BitVec.access, getElem!_pos x i bound, BitVec.getLsbD_ofBool]
  simp [BitVec.getLsbD_extractLsb', ← BitVec.getLsbD_eq_getElem]

theorem immediate_even pc imm (aligned : is_aligned_vaddr (.Virtaddr pc) 2 = true)
    (even : TargetEven pc imm) : Encodable imm := by
  have zero := KptFetch.bit0 pc aligned
  have one : (target pc imm).getLsbD 0 = false := by
    have h := congrArg (fun x : BitVec 1 => x.getLsbD 0) even
    simpa [Sail.BitVec.access,← BitVec.getLsbD_eq_getElem] using h
  have two : pc.getLsbD 0 = false := by
    have h := congrArg (fun x : BitVec 1 => x.getLsbD 0) zero
    simpa [Sail.BitVec.access,← BitVec.getLsbD_eq_getElem] using h
  simp only [target,BitVec.getLsbD_add (by decide : 0 < 64),BitVec.carry_zero,
    sign_extend,Sail.BitVec.signExtend,BitVec.getLsbD_signExtend,two] at one
  have low : imm.getLsbD 0 = false := by simpa using one
  simp [Encodable,Sail.BitVec.access,← BitVec.getLsbD_eq_getElem,low]

theorem low_slice imm lo len (bound : lo + len ≤ 12) :
    (encoding imm).extractLsb' lo len = (0xef#12).extractLsb' lo len := by
  unfold encoding
  simp only [BitVec.append_eq]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  rfl

theorem slice_low imm : (encoding imm).extractLsb' 0 12 = 0xef#12 := low_slice imm 0 12 (by decide)

theorem opcode imm : Sail.BitVec.extractLsb (encoding imm) 6 0 = 0x6f#7 :=
  low_slice imm 0 7 (by decide)

theorem destination imm : Sail.BitVec.extractLsb (encoding imm) 11 7 = 1#5 :=
  low_slice imm 7 5 (by decide)

theorem base imm : isRVC (KernelTextDatum.lowHalf (encoding imm)) = false := by
  have low := low_slice imm 0 2 (by decide)
  have slice : (KernelTextDatum.lowHalf (encoding imm)).extractLsb' 0 2 = 3#2 := by
    rw [KernelTextDatum.lowHalf,BitVec.extractLsb'_extractLsb'_of_le (by decide)]
    exact low
  change LeanPaperStock.Functions.not (((KernelTextDatum.lowHalf (encoding imm)).extractLsb' 0 2) == 3#2) = false
  rw [slice]
  rfl

theorem nested_slice {w : Nat} (x : BitVec w) start len substart sublen (bound : substart + sublen ≤ len) :
    (x.extractLsb' start len).extractLsb' substart sublen = x.extractLsb' (start + substart) sublen := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have within : substart + j < len := by omega
  simp [hj,within,Nat.add_assoc]

theorem encoder [Platform] imm (even : Encodable imm) :
    encdec_forwards (instruction imm) = pure (encoding imm) := by
  have low : Sail.BitVec.extractLsb imm 0 0 = 0#1 :=
    (access_extract imm 0 (by decide)).symm.trans even
  unfold instruction encdec_forwards
  simp only [low,beq_self_eq_true,↓reduceIte]
  simp only [Sail.BitVec.extractLsb,BitVec.extractLsb]
  simp only [Nat.reduceSub,Nat.reduceAdd]
  simp only [nested_slice imm 1 20 19 1 (by decide),nested_slice imm 1 20 0 10 (by decide),
    nested_slice imm 1 20 10 1 (by decide),nested_slice imm 1 20 11 8 (by decide)]
  rfl

theorem field_sign imm : Sail.BitVec.extractLsb (encoding imm) 31 31 = imm.extractLsb' 20 1 := by
  simp only [Sail.BitVec.extractLsb,BitVec.extractLsb,encoding,BitVec.append_eq]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem field_ten imm : Sail.BitVec.extractLsb (encoding imm) 30 21 = imm.extractLsb' 1 10 := by
  simp only [Sail.BitVec.extractLsb,BitVec.extractLsb,encoding,BitVec.append_eq]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem field_middle imm : Sail.BitVec.extractLsb (encoding imm) 20 20 = imm.extractLsb' 11 1 := by
  simp only [Sail.BitVec.extractLsb,BitVec.extractLsb,encoding,BitVec.append_eq]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem field_eight imm : Sail.BitVec.extractLsb (encoding imm) 19 12 = imm.extractLsb' 12 8 := by
  simp only [Sail.BitVec.extractLsb,BitVec.extractLsb,encoding,BitVec.append_eq]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem reassemble imm (even : Encodable imm) :
    BitVec.append (BitVec.append (BitVec.append (BitVec.append
      (imm.extractLsb' 20 1) (imm.extractLsb' 12 8)) (imm.extractLsb' 11 1))
      (imm.extractLsb' 1 10)) 0#1 = imm := by
  have low : imm.extractLsb' 0 1 = 0#1 := (access_extract imm 0 (by decide)).symm.trans even
  rw [← low]
  simp only [BitVec.append_eq]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_eq_self

end Xv6.Kernel.KptJal
