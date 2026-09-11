import MachCSL.Logic.SpinlockBootResourcesProofs
import MachCSL.Logic.EraSpec

namespace MachCSL.Logic.SpinlockBootResources
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine

/-- Reuse precisely the existing era's heap, view and history capacities. -/
def storeCapacity {GF : BundledGFunctors} (capacity : Era.Capacity GF) : TsoStore.Capacity GF :=
  ⟨capacity.heap, capacity.views, capacity.history⟩

def storeNames (era : Era.Record) : TsoStore.Names := ⟨era.tsoNames, era.metadata⟩

/-- This is a separating resource extraction from the actual allocation
result. It neither allocates replacement cells nor consumes the log receipt. -/
theorem boot_resources {GF : BundledGFunctors} (capacity : Era.Capacity GF)
    (era : Era.Record) (g : State) (facts : BootFacts SpinlockImage.image g)
    (memory : Tso.AddressMap Byte) (decoded : Memory.FiniteMap.decode memory = g.memory) :
    iprop(Tso.Interp.bootClients capacity.tso era.tsoNames memory ⊢
      windows (storeCapacity capacity) (storeNames era) ∗
      remainder (storeCapacity capacity) (storeNames era) memory ∗
      Tso.Views.natLB capacity.views era.logLength 0) := by
  unfold Tso.Interp.bootClients Era.Capacity.tso
  iintro ⟨Hb, Ht, Hlength⟩
  have extracted := extract_initial (storeCapacity capacity) (storeNames era) g facts memory decoded
  unfold BootWindow.mapBytes BootWindow.mapTimes storeCapacity storeNames at extracted
  ihave ⟨Hwindows, Hrest⟩ := extracted $$ [Hb Ht]
  · iframe
  · unfold storeCapacity storeNames
    isimp only [Era.Record.tsoNames] at Hlength
    iframe

theorem remainder_byte_lookup (memory : Tso.AddressMap Byte) (a : PhysicalAddress)
    (outside : a ∉ BootWindow.wordKeys words) :
    Iris.Std.PartialMap.get? (JalBootResources.deleteKeys memory (BootWindow.wordKeys words)) a =
      Iris.Std.PartialMap.get? memory a :=
  BootWindow.lookup_deleteKeys memory _ a outside

theorem remainder_time_lookup (memory : Tso.AddressMap Byte) (a : PhysicalAddress)
    (outside : a ∉ BootWindow.wordKeys words) :
    Iris.Std.PartialMap.get?
        (JalBootResources.deleteKeys (Tso.Interp.bootTimestamps memory) (BootWindow.wordKeys words)) a =
      Iris.Std.PartialMap.get? (Tso.Interp.bootTimestamps memory) a :=
  BootWindow.lookup_deleteKeys _ _ a outside

end MachCSL.Logic.SpinlockBootResources
