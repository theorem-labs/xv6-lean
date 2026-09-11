import MachCSL.Logic.TsoContextWordDefs
import MachCSL.Logic.MemoryReadWPDefs

/-! Physical registered-context word reads through the actual V1 event.
Request metadata is preserved; eight bytes is the event's dependent index. -/
namespace MachCSL.Logic.TsoContextReadWP
open Iris Iris.BI MachCSL.Machine

@[reducible] def contextCapacity {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF) :
    TsoContext.Capacity GF := ⟨capacity.era.heap, capacity.era.views, capacity.era.history⟩
@[reducible] def contextNames (era : Era.Record) : TsoContext.Names :=
  ⟨era.tsoNames, era.metadata⟩

abbrev running {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId) : IProp GF :=
  TsoContext.ownContext (contextCapacity capacity) (contextNames era) cpu ξ

abbrev wordPointsto {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (ξ : TsoContext.CtxId) (a : Memory.PhysicalAddress)
    (dq : DFrac) (word : BitVec 64) : IProp GF :=
  TsoContextWord.pointsto (contextCapacity capacity) (contextNames era) ξ a dq word

end MachCSL.Logic.TsoContextReadWP
