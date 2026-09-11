import Xv6.Kernel.KernelTextImageDefs
import Xv6.Kernel.MycpuBootResourcesDefs

/-! One sparse carve of the actual boot clients, followed by native byte and
timestamp persistence. No code byte is allocated twice, and text holes stay
in the exact remainder. Static-map/tree installation is separate. -/
namespace Xv6.Kernel.KernelTextBoot
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KernelTextImage.Capacity
abbrev sourceMap := KernelTextImage.sourceMap
abbrev address := KernelTextImage.address
abbrev value := KernelTextImage.value
abbrev runs := Xv6.Generated.KernelMaps.codeRuns

/-- Payloads come directly from the seven imported source runs. The byte
bridge below is a checked arithmetic theorem, not an extractor assumption. -/
def descriptor (run : ByteRun) : BootWindow.Word :=
  ⟨address run.base, run.length, BitVec.ofNat (8 * run.length) run.payload⟩
def descriptors : List BootWindow.Word := runs.map descriptor
def keys : List PhysicalAddress := BootWindow.wordKeys descriptors

variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev storeCapacity : TsoStore.Capacity GF := MycpuBootResources.storeCapacity capacity.machine.era
abbrev storeNames := MycpuBootResources.storeNames

/-- Both full original fragments remain linear until persist is invoked. -/
def rawText (era : Era.Record) : IProp GF :=
  iprop([∗list] w ∈ descriptors,
    TsoStore.storedWindow (storeCapacity capacity) (storeNames era) w.address w.size w.value 0)

/-- Literal remainder after removing exactly the sparse text keys from
both client maps. Metadata tokens, including those for text, are elsewhere
in otherClients and remain untouched. -/
def remainder (era : Era.Record) (memory : Tso.AddressMap Byte) : IProp GF :=
  iprop(BootWindow.mapBytes capacity.machine.era.heap.ledger era.heap
      (JalBootResources.deleteKeys memory keys) ∗
    BootWindow.mapTimes capacity.machine.era.heap.ledger era.timestamps
      (JalBootResources.deleteKeys (Tso.Interp.bootTimestamps memory) keys))

abbrev otherClients (era : Era.Record) (memory : Tso.AddressMap Byte)
    (g : State) (diskBytes : Nat) : IProp GF :=
  MycpuBootResources.otherClients capacity.machine.era era memory g diskBytes

/-- Every non-text byte/timestamp client and every other era client survives. -/
def retained (era : Era.Record) (memory : Tso.AddressMap Byte)
    (g : State) (diskBytes : Nat) : IProp GF :=
  iprop(remainder capacity era memory ∗ Tso.Views.natLB capacity.machine.era.views era.logLength 0 ∗
    otherClients capacity era memory g diskBytes)

end Xv6.Kernel.KernelTextBoot
