import Xv6.Kernel.KernelTextBootPureProofs

namespace Xv6.Kernel.KernelTextBoot
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
attribute [local irreducible] descriptors
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem extract_initial era (g : State) (memory : Tso.AddressMap Byte)
    (facts : BootFacts Xv6.Machine.bootImage g) (decoded : FiniteMap.decode memory = g.memory) :
    iprop(BootWindow.mapBytes capacity.machine.era.heap.ledger era.heap memory ∗
      BootWindow.mapTimes capacity.machine.era.heap.ledger era.timestamps (Tso.Interp.bootTimestamps memory) ⊢
      rawText capacity era ∗ remainder capacity era memory) := by
  have bounds (w : BootWindow.Word) (member : w ∈ descriptors) : w.size ≤ 2^64 := by
    rw [descriptors] at member
    obtain ⟨run, runMember, rfl⟩ := List.mem_map.mp member
    have := run_bounds run runMember
    change run.length ≤ 2^64
    omega
  exact BootWindow.extract_words (storeCapacity capacity) (storeNames era) descriptors 0 unique bounds ram
    memory (Tso.Interp.bootTimestamps memory) (boot_lookup g memory facts decoded) (boot_times g memory facts decoded)

theorem extract era g memory diskBytes
    (facts : BootFacts Xv6.Machine.bootImage g) (decoded : FiniteMap.decode memory = g.memory) :
    iprop(Era.bootClients capacity.machine.era era memory g diskBytes ⊢
      rawText capacity era ∗ retained capacity era memory g diskBytes) := by
  unfold Era.bootClients Tso.Interp.bootClients Era.Capacity.tso
  iintro ⟨Hregs, ⟨Hb, Ht, Hlength⟩, Hmeta, Hdevices, Hdisk, Hresv⟩
  have extracted := extract_initial capacity era g memory facts decoded
  unfold BootWindow.mapBytes BootWindow.mapTimes at extracted
  isimp only [Era.Record.tsoNames] at Hb
  isimp only [Era.Record.tsoNames] at Ht
  ihave ⟨Htext, Hrest⟩ := extracted $$ [Hb Ht]
  · iframe
  unfold retained otherClients MycpuBootResources.otherClients
  isimp only [Era.Record.tsoNames] at Hlength
  iframe

end Xv6.Kernel.KernelTextBoot
