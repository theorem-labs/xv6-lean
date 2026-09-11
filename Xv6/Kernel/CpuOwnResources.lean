import Xv6.Kernel.CpuOwnPure
import Xv6.Kernel.KernelDatumLink
import MachCSL.Logic.LockSetProofs
import MachCSL.Logic.SupervisorBitsProofs
import MachCSL.Logic.TsoContextBytesProofs

namespace Xv6.Kernel.CpuOwn
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance word4_timeless era ξ address dq value : Timeless (word4 capacity era ξ address dq value) := by
  unfold word4 KernelDatum.byte KernelDatum.physicalByte
  infer_instance
instance curProc_timeless era cpu ξ process : Timeless (curProc capacity era cpu ξ process) := by
  unfold curProc KernelDatum.word KernelDatum.byte KernelDatum.physicalByte
  infer_instance
instance count_timeless era cpu depth baseEnabled : Timeless (count capacity era cpu depth baseEnabled) := by
  letI := capacity.execution.bits
  unfold count SupervisorBits.countBit SupervisorBits.bit
  infer_instance
instance cells_timeless era cpu ξ depth baseEnabled process :
    Timeless (cells capacity era cpu ξ depth baseEnabled process) := by
  unfold cells
  cases depth <;> infer_instance
instance hartCsrs_timeless era cpu : Timeless (hartCsrs capacity era cpu) := by
  unfold hartCsrs
  infer_instance
instance privateState_timeless era cpu ξ depth baseEnabled process held :
    Timeless (privateState capacity era cpu ξ depth baseEnabled process held) := by
  unfold privateState LockSet.cpuLevel
  infer_instance
instance ownOff_timeless era cpu ξ depth baseEnabled process held :
    Timeless (ownOff capacity era cpu ξ depth baseEnabled process held) := by
  unfold ownOff
  infer_instance

theorem word4_unfold era ξ address dq value :
    iprop(word4 capacity era ξ address dq value ⊣⊢
      ⌜Aligned4 address⌝ ∗ [∗list] j ∈ List.range 4,
        KernelDatum.byte capacity.execution.translation era .identity ξ
          (addressAdd address j) dq (nthByte value j)) := .rfl

/-- Physical access preserves the four individual mapping-funded closures. -/
theorem word4_access era ξ address dq value :
    iprop(word4 capacity era ξ address dq value ⊢
      ⌜Aligned4 address⌝ ∗ TsoContextBytesReadWP.window capacity.machine era ξ address 4 dq value ∗
      (∀ replacement : SmallWord, TsoContextBytesReadWP.window capacity.machine era ξ address 4 dq replacement -∗
        word4 capacity era ξ address dq replacement)) := by
  unfold word4
  iintro ⟨#Halign,Hbytes⟩
  ihave Hsplit : iprop([∗list] j ∈ List.range 4,
      KernelDatum.physicalByte capacity.execution.translation era ξ (addressAdd address j) dq (nthByte value j) ∗
      (∀ replacement : Byte,
        KernelDatum.physicalByte capacity.execution.translation era ξ (addressAdd address j) dq replacement -∗
        KernelDatum.byte capacity.execution.translation era .identity ξ (addressAdd address j) dq replacement)) $$ [Hbytes]
  · iapply BigSepL.bigSepL_mono $$ Hbytes
    intro k j lookup
    exact KernelDatum.identity_access capacity.execution.translation era ξ (addressAdd address j) dq (nthByte value j)
  ihave ⟨Hphysical,Hclose⟩ := BigSepL.bigSepL_sep_eqv.mp $$ Hsplit
  isplit
  · iexact Halign
  isplitl [Hphysical]
  · unfold TsoContextBytesReadWP.window TsoContextBytes.window
    iunfold KernelDatum.physicalByte at Hphysical
    iexact Hphysical
  · iintro %replacement Hphysical
    isplit
    · iexact Halign
    isimp only [TsoContextBytesReadWP.window,TsoContextBytes.window] at Hphysical
    ihave Hpairs := BigSepL.bigSepL_sep_eqv.mpr $$ [Hclose Hphysical]
    · iframe Hclose Hphysical
    iapply BigSepL.bigSepL_mono $$ Hpairs
    intro k j lookup
    iintro ⟨Hclose,Hphysical⟩
    iunfold KernelDatum.physicalByte at Hclose
    iapply Hclose $$ %(nthByte replacement j) Hphysical

theorem count_init era cpu : iprop(off capacity era cpu ⊣⊢ count capacity era cpu 0 false) := .rfl

theorem count_retune era cpu depth baseEnabled replacement :
    iprop(count capacity era cpu (depth + 1) baseEnabled ⊣⊢ count capacity era cpu (depth + 1) replacement) := by
  simp only [count,SupervisorBits.countBit,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false]
  exact .rfl

theorem count_pack era cpu depth baseEnabled :
    iprop(off capacity era cpu ⊣⊢ count capacity era cpu (depth + 1) baseEnabled) := by
  simp only [count,SupervisorBits.countBit,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false]
  exact .rfl

theorem count_pop era cpu depth :
    iprop(count capacity era cpu (depth + 1) false ⊣⊢ count capacity era cpu depth false) := by
  cases depth <;> exact .rfl

theorem count_dec era cpu depth baseEnabled :
    iprop(count capacity era cpu (depth + 2) baseEnabled ⊣⊢ count capacity era cpu (depth + 1) baseEnabled) := by
  simp only [count,SupervisorBits.countBit,Nat.add_eq_zero_iff,Nat.reduceEqDiff,and_false,ite_false]
  exact .rfl

theorem count_push era cpu depth baseEnabled :
    iprop(⊢ off capacity era cpu -∗ count capacity era cpu depth baseEnabled -∗
      ⌜depth = 0 → baseEnabled = false⌝ ∗ off capacity era cpu ∗ count capacity era cpu (depth + 1) baseEnabled) := by
  iintro Hoff Hcount
  isimp only [off,SieOffCapability.off,SupervisorBits.offToken] at Hoff
  iunfold count at Hcount
  ihave %index := (SupervisorBits.actual capacity.execution.supervisorBits).countIndex
    (SupervisorBits.namesOfEra era cpu) depth baseEnabled false $$ Hoff Hcount
  isplitr
  · ipureintro
    intro zero
    simpa [zero] using index
  · cases depth with
    | zero =>
      have disabled : baseEnabled = false := by simpa using index
      subst baseEnabled
      isimp [SupervisorBits.countBit,SupervisorBits.armBit,SupervisorBits.sieBit] at Hoff Hcount
      simp [off,SieOffCapability.off,SupervisorBits.offToken,SupervisorBits.armBit,count,SupervisorBits.countBit,SupervisorBits.sieBit]
      iframe
    | succ depth =>
      isimp [SupervisorBits.countBit,SupervisorBits.armBit,SupervisorBits.sieBit] at Hoff Hcount
      simp [off,SieOffCapability.off,SupervisorBits.offToken,SupervisorBits.armBit,count,SupervisorBits.countBit,SupervisorBits.sieBit]
      iframe

end Xv6.Kernel.CpuOwn
