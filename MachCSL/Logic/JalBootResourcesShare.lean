import MachCSL.Logic.JalBootResourcesDefs
import MachCSL.Logic.TsoReadProofs

namespace MachCSL.Logic.JalBootResources
open Iris Iris.Std Iris.BI MachCSL.Machine

/-- Eight equal positive fractions, represented by three exact halvings. -/
def codeShare : Qp := ((1 : Qp).half.half).half

def sharedCode {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) : IProp GF :=
  iprop([∗set] cpu ∈ GlobalRegisters.allCPUs, EventWP.codeResources capacity era (.own codeShare))

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

theorem byte_halves (era : Era.Record) (q : Qp) :
    iprop(TsoRead.byteWindow capacity.era.heap.ledger era.heap jalImage.vector 4 (.own q) 0x6f#32 ⊣⊢
      TsoRead.byteWindow capacity.era.heap.ledger era.heap jalImage.vector 4 (.own q.half) 0x6f#32 ∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap jalImage.vector 4 (.own q.half) 0x6f#32) := by
  haveI : Fractional (fun p => TsoRead.byteWindow capacity.era.heap.ledger era.heap jalImage.vector 4 (.own p) 0x6f#32) := by
    unfold TsoRead.byteWindow
    infer_instance
  have h := Fractional.fractional (Φ := fun p => TsoRead.byteWindow capacity.era.heap.ledger era.heap jalImage.vector 4 (.own p) 0x6f#32) q.half q.half
  rw [Qp.half_add_half] at h
  exact h

theorem code_halves (era : Era.Record) (q : Qp) :
    iprop(⊢ EventWP.codeResources capacity era (.own q) -∗
      EventWP.codeResources capacity era (.own q.half) ∗ EventWP.codeResources capacity era (.own q.half)) := by
  unfold EventWP.codeResources
  iintro ⟨Hbytes, #Hpristine⟩
  ihave ⟨Hleft, Hright⟩ := (byte_halves capacity era q).1 $$ Hbytes
  iframe Hleft Hright
  isplit
  · iexact Hpristine
  · iexact Hpristine

theorem code_eight (era : Era.Record) :
    iprop(⊢ EventWP.codeResources capacity era (.own 1) -∗ sharedCode capacity era) := by
  iintro H
  ihave ⟨H1, H2⟩ := code_halves capacity era 1 $$ H
  ihave ⟨H11, H12⟩ := code_halves capacity era (1 : Qp).half $$ H1
  ihave ⟨H21, H22⟩ := code_halves capacity era (1 : Qp).half $$ H2
  ihave ⟨H111, H112⟩ := code_halves capacity era (1 : Qp).half.half $$ H11
  ihave ⟨H121, H122⟩ := code_halves capacity era (1 : Qp).half.half $$ H12
  ihave ⟨H211, H212⟩ := code_halves capacity era (1 : Qp).half.half $$ H21
  ihave ⟨H221, H222⟩ := code_halves capacity era (1 : Qp).half.half $$ H22
  unfold sharedCode GlobalRegisters.allCPUs codeShare
  have set_eq : (Iris.Std.LawfulSet.ofList (List.finRange 8) : GlobalRegisters.CPUSet) =
      _root_.Std.ExtTreeSet.ofList (List.finRange 8) := by
    apply _root_.Std.ExtTreeSet.ext_mem
    intro cpu
    constructor
    · intro _; exact GlobalRegisters.mem_allCPUs cpu
    · intro _; exact Iris.Std.LawfulSet.mem_ofList.mp (List.mem_finRange cpu)
  rw [← set_eq]
  iapply (BigSepS.bigSepS_of_list (S := GlobalRegisters.CPUSet) (List.nodup_finRange 8)).2
  iapply BigSepL.bigSepL_replicate.1
  simp only [List.length_finRange, List.replicate_succ, List.replicate_zero]
  iframe
  iapply BigSepL.bigSepL_nil.mpr
  itrivial

end MachCSL.Logic.JalBootResources
