import Xv6.Kernel.KptFetchPlanProofs
import Xv6.Kernel.KernelTextDatumWindowProofs

namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem low_extend (half : BitVec 16) : KernelTextDatum.lowHalf (half.setWidth 32) = half := by
  apply BitVec.eq_of_toNat_eq
  simp [KernelTextDatum.lowHalf,BitVec.extractLsb'_toNat,BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt half.isLt]

theorem parts_addresses pc word :
    (parts pc word).map Chunk.address = chunks pc (classified word) := by
  by_cases four : is_aligned_vaddr (.Virtaddr pc) 4 = true <;>
    by_cases rvc : isRVC (KernelTextDatum.lowHalf word) = true <;>
    simp [parts,classified,chunks,four,rvc]

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- The literal word is only a finite plan index. The compressed two-byte
case owns exactly two bytes; no fabricated upper half enters a memory rule. -/
theorem select_word era tier pc result :
    iprop(instrBytes capacity era tier pc result ⊢
      ∃ word : BitVec 32, ⌜classified word = result ∧ is_aligned_vaddr (.Virtaddr pc) 2 = true⌝ ∗
        chunkWindows capacity era tier (parts pc word)) := by
  iintro Hbytes
  iunfold instrBytes at Hbytes
  icases Hbytes with ⟨%aligned,Hbytes⟩
  cases result with
  | F_Base word =>
    icases Hbytes with ⟨%notRvc,Hword⟩
    iexists word
    isplit
    · ipureintro; exact ⟨by simp [classified,notRvc],aligned⟩
    · unfold parts
      split
      · iunfold chunkWindows
        isimp only [BigSepL.bigSepL_cons.to_eq,BigSepL.bigSepL_nil.to_eq,sep_emp.to_eq]
        iexact Hword
      · simp only [notRvc,Bool.false_eq_true,↓reduceIte]
        ihave ⟨Hlow,Hhigh⟩ := (KernelTextDatum.split_four capacity era tier pc .discard word).mp $$ Hword
        iunfold chunkWindows
        isimp only [BigSepL.bigSepL_cons.to_eq,BigSepL.bigSepL_nil.to_eq,sep_emp.to_eq]
        iframe Hlow Hhigh
  | F_RVC half =>
    icases Hbytes with ⟨%rvc,Hword⟩
    by_cases four : is_aligned_vaddr (.Virtaddr pc) 4 = true
    · isimp only [four,↓reduceIte] at Hword
      icases Hword with ⟨%word,%low,Hword⟩
      iexists word
      isplit
      · ipureintro; exact ⟨by simp [classified,low,rvc],aligned⟩
      · simp only [parts,four,↓reduceIte]
        iunfold chunkWindows
        isimp only [BigSepL.bigSepL_cons.to_eq,BigSepL.bigSepL_nil.to_eq,sep_emp.to_eq]
        iexact Hword
    · have notFour := Bool.eq_false_iff.mpr four
      isimp only [notFour,Bool.false_eq_true,↓reduceIte] at Hword
      iexists half.setWidth 32
      isplit
      · ipureintro; exact ⟨by simp [classified,low_extend,rvc],aligned⟩
      · simp only [parts,notFour,Bool.false_eq_true,↓reduceIte,low_extend,rvc]
        iunfold chunkWindows
        isimp only [BigSepL.bigSepL_cons.to_eq,BigSepL.bigSepL_nil.to_eq,sep_emp.to_eq]
        iexact Hword
  | F_Error _ => icases Hbytes with ⟨⟩
  | F_Ext_Error _ => icases Hbytes with ⟨⟩

end Xv6.Kernel.KptFetch
