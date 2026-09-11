import Xv6.Kernel.PushOffStackSpec
import Xv6.Kernel.MycpuBareSourceResources
import Xv6.Kernel.MycpuBareGeometry
import Xv6.Kernel.KernelStackLink

namespace Xv6.Kernel.PushOffStack
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem identity_word era ξ va old :
    iprop(KernelDatum.word capacity.translation era .identity ξ va (.own 1) old ⊢
      ⌜TsoContextWord.Aligned va ∧ SupervisorPhysical.RamRange va 8⌝ ∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ va (.own 1) old ∗ closeIdentity capacity era ξ va) := by
  iintro Hword
  ihave ⟨Hword,Hclose⟩ := MycpuBareSource.identity_word capacity era ξ va old $$ Hword
  ihave %aligned := TsoContextWord.aligned (TsoContextReadWP.contextCapacity capacity.machine)
    (TsoContextReadWP.contextNames era) ξ va (.own 1) old $$ Hword
  ihave %range := MycpuBare.word_range capacity.machine era ξ va (.own 1) old $$ Hword
  iunfold closeIdentity
  iunfold MycpuBareSource.closeWord at Hclose
  iframe Hword Hclose
  ipureintro
  exact ⟨aligned,range⟩

theorem frame_four era tier ξ entrySP :
    iprop(KernelStack.own capacity.translation era tier ξ entrySP 4 ⊣⊢ ∃ words gap,
      savedWords capacity era tier ξ entrySP words ∗
      KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk entrySP 4) (.own 1) gap) := by
  rw [((KernelStack.nativeSpec capacity.translation).append era tier ξ entrySP 2 2).to_eq,
    ((KernelStack.nativeSpec capacity.translation).two era tier ξ entrySP).to_eq,
    ((KernelStack.nativeSpec capacity.translation).two era tier ξ (KernelStack.paStk entrySP 2)).to_eq]
  have first : KernelStack.paStk (KernelStack.paStk entrySP 2) 1 = KernelStack.paStk entrySP 3 := StackPhysical.paStk_assoc entrySP 2 1
  have second : KernelStack.paStk (KernelStack.paStk entrySP 2) 2 = KernelStack.paStk entrySP 4 := StackPhysical.paStk_assoc entrySP 2 2
  rw [first,second]
  constructor
  · iintro ⟨⟨%ra,%s0,Hra,Hs0⟩,⟨%s1,%gap,Hs1,Hgap⟩⟩
    iexists (fun slot => match slot with | .ra => ra | .s0 => s0 | .s1 => s1), gap
    iunfold savedWords
    iframe
  · iintro ⟨%words,%gap,Hsaved,Hgap⟩
    iunfold savedWords at Hsaved
    icases Hsaved with ⟨Hra,Hs0,Hs1⟩
    isplitl [Hra Hs0]
    · iexists words .ra, words .s0
      iframe
    · iexists words .s1, gap
      iframe

theorem resourceSpec : ResourceSpec capacity := ⟨identity_word capacity,frame_four capacity⟩

end Xv6.Kernel.PushOffStack
