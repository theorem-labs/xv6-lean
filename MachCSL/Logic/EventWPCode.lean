import MachCSL.Logic.EventWPDefs
import MachCSL.Machine.JalLoopPlanFetch

/-! Concrete extraction/restoration for the four bytes read by the actual JAL
fetch certificate. It assumes no callee WP and no ownership of the rest of RAM. -/
namespace MachCSL.Logic.EventWP
open Iris Iris.BI MachCSL.Machine

def codeResources {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (dq : DFrac) : IProp GF :=
  iprop(TsoRead.byteWindow capacity.era.heap.ledger era.heap jalImage.vector 4 dq 0x6f#32 ∗
    TsoRead.pristineWindow capacity.era.heap.ledger era.timestamps jalImage.vector 4)

theorem codeRamAccess {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (dq : DFrac) :
    RamAccess capacity era JalLoopPlan.CodeRead dq (codeResources capacity era dq) where
  access := by
    intro n req word allowed
    obtain ⟨rfl, address, rfl⟩ := allowed
    rw [address]
    unfold codeResources
    iintro ⟨Hbytes, Hpristine⟩
    iframe Hbytes Hpristine
    iintro Hbytes Hpristine
    iframe

end MachCSL.Logic.EventWP
