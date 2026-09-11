import MachCSL.Logic.SpinlockCodeDefs

namespace MachCSL.Logic.SpinlockCode
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

theorem codeAccess (era : Era.Record) (dq : DFrac) (i : Fin 17) :
    EventWP.RamAccess capacity era (SpinlockFetch.CodeRead i) dq (allCode capacity era dq) where
  access := by
    intro n req word allowed
    obtain ⟨rfl, address, rfl⟩ := allowed
    rw [address]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    iintro H
    iunfold allCode at H
    have found : (List.finRange 17)[i.val]? = some i := by simp; apply Fin.ext; rfl
    ihave ⟨Hi, Hrest⟩ := (BigSepL.bigSepL_delete_cond found).mp $$ H
    iunfold instruction at Hi
    icases Hi with ⟨Hb, Ht⟩
    iframe Hb Ht
    iintro Hb Ht
    unfold allCode
    iapply (BigSepL.bigSepL_delete_cond found).mpr
    iframe Hrest
    unfold instruction
    iframe

theorem instruction_halves (era : Era.Record) (q : Qp) (i : Fin 17) :
    instruction capacity era (.own q) i ⊢
      instruction capacity era (.own q.half) i ∗ instruction capacity era (.own q.half) i := by
  haveI : Fractional (fun p => TsoRead.byteWindow capacity.era.heap.ledger era.heap
      (SpinlockImage.instructionAddress i) 4 (.own p) (SpinlockImage.word i)) := by
    unfold TsoRead.byteWindow
    infer_instance
  have law := Fractional.fractional (Φ := fun p => TsoRead.byteWindow capacity.era.heap.ledger era.heap
    (SpinlockImage.instructionAddress i) 4 (.own p) (SpinlockImage.word i)) q.half q.half
  rw [Qp.half_add_half] at law
  unfold instruction
  iintro ⟨Hb, #Ht⟩
  ihave ⟨Hleft, Hright⟩ := law.mp $$ Hb
  iframe Hleft Hright
  isplit <;> iexact Ht

theorem halves (era : Era.Record) (q : Qp) :
    allCode capacity era (.own q) ⊢ allCode capacity era (.own q.half) ∗ allCode capacity era (.own q.half) := by
  unfold allCode
  iintro H
  iapply BigSepL.bigSepL_sep_eqv.mp
  iapply BigSepL.bigSepL_mono $$ H
  intro k i found
  exact instruction_halves capacity era q i

theorem eight (era : Era.Record) : allCode capacity era (.own 1) ⊢ shared capacity era := by
  iintro H
  ihave ⟨H1, H2⟩ := halves capacity era 1 $$ H
  ihave ⟨H11, H12⟩ := halves capacity era (1 : Qp).half $$ H1
  ihave ⟨H21, H22⟩ := halves capacity era (1 : Qp).half $$ H2
  ihave ⟨H111, H112⟩ := halves capacity era (1 : Qp).half.half $$ H11
  ihave ⟨H121, H122⟩ := halves capacity era (1 : Qp).half.half $$ H12
  ihave ⟨H211, H212⟩ := halves capacity era (1 : Qp).half.half $$ H21
  ihave ⟨H221, H222⟩ := halves capacity era (1 : Qp).half.half $$ H22
  unfold shared GlobalRegisters.allCPUs JalBootResources.codeShare
  have set_eq : (Iris.Std.LawfulSet.ofList (List.finRange 8) : GlobalRegisters.CPUSet) =
      _root_.Std.ExtTreeSet.ofList (List.finRange 8) := by
    apply _root_.Std.ExtTreeSet.ext_mem
    intro cpu
    constructor
    · intro _; exact GlobalRegisters.mem_allCPUs cpu
    · intro _; exact Iris.Std.LawfulSet.mem_ofList.mp (List.mem_finRange cpu)
  rw [← set_eq]
  iapply (BigSepS.bigSepS_of_list (S := GlobalRegisters.CPUSet) (List.nodup_finRange 8)).mpr
  iapply BigSepL.bigSepL_replicate.mp
  simp only [List.length_finRange, List.replicate_succ, List.replicate_zero]
  iframe
  iapply BigSepL.bigSepL_nil.mpr
  itrivial

theorem mint_instruction (era : Era.Record) (i : Fin 17) :
    TsoStore.storedWindow (MemoryWriteWP.storeCapacity capacity) (MemoryWriteWP.storeNames era)
      (SpinlockImage.instructionAddress i) 4 (SpinlockImage.word i) 0 ⊢
      |==> instruction capacity era (.own 1) i := by
  iintro H
  ihave ⟨Hb, Ht⟩ := (BootWindow.storedWindow_split (MemoryWriteWP.storeCapacity capacity)
    (MemoryWriteWP.storeNames era) (SpinlockImage.instructionAddress i) 4 (SpinlockImage.word i) 0).mp $$ H
  isimp only [MemoryWriteWP.storeCapacity, MemoryWriteWP.storeNames, Era.Record.tsoNames] at Hb Ht
  iunfold BootWindow.timeWindow at Ht
  have update := TsoRead.pristine_window_mint capacity.era.heap.ledger era.timestamps
    (SpinlockImage.instructionAddress i) 4
  unfold TsoRead.initialTimestampWindow at update
  imod update $$ Ht with Ht
  imodintro
  unfold instruction
  iframe Hb Ht

theorem mint (era : Era.Record) :
    SpinlockBootResources.codeWindows (MemoryWriteWP.storeCapacity capacity) (MemoryWriteWP.storeNames era) ⊢
      |==> allCode capacity era (.own 1) := by
  unfold SpinlockBootResources.codeWindows SpinlockBootResources.codeWords allCode
  have eq : List.ofFn SpinlockBootResources.codeWord = (List.finRange 17).map SpinlockBootResources.codeWord := by
    rfl
  rw [eq, BigSepL.bigSepL_map]
  iintro H
  iapply BigSepL.bigSepL_bupd
  iapply BigSepL.bigSepL_mono $$ H
  intro k i found
  exact mint_instruction capacity era i

theorem mint_shared (era : Era.Record) :
    SpinlockBootResources.codeWindows (MemoryWriteWP.storeCapacity capacity) (MemoryWriteWP.storeNames era) ⊢
      |==> shared capacity era := by
  iintro H
  imod mint capacity era $$ H with H
  imodintro
  iapply eight capacity era $$ H

end MachCSL.Logic.SpinlockCode
