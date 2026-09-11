import Xv6.Kernel.KernelTextDatumDefs
import Xv6.Kernel.KernelMapStaticDefs
import Xv6.Kernel.MycpuKptFetchDefs
import Xv6.Generated.KernelMapsCode

/-! Persistent kernel text, indexed by the exact sparse source byte lookup.
The assertion owns native RX/pristine bytes; absent source addresses impose
no obligation and are never filled by a default byte. -/
namespace Xv6.Kernel.KernelTextImage
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KernelTextDatum.Capacity
abbrev Tier := KernelTextDatum.Tier
abbrev sourceMap := runMap Xv6.Generated.KernelMaps.codeRuns

def address (a : Int) : PhysicalAddress := BitVec.ofInt 64 a
abbrev value := Xv6.Machine.byteOfUInt8

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

/-- Extensional form of the source finite persistent byte conjunction. No
hart, TSO context, decoder state, translation or execution premise occurs. -/
noncomputable def text (tier : Tier) : IProp GF :=
  iprop(∀ a b, ⌜sourceMap a = some b⌝ -∗
    KernelTextDatum.byte capacity era tier (address a) .discard (value b))

/-- Existing physical text bytes and discarded timestamp-zero receipts,
before attaching the actual static map's RX claims. -/
noncomputable def physicalText : IProp GF :=
  iprop(∀ a b, ⌜sourceMap a = some b⌝ -∗
    KernelTextDatum.rawByte capacity era (address a) .discard (value b) ∗
    KernelTextDatum.pristine capacity era (address a))

/-- A finite representation with exactly one obligation for each byte in
the seven imported source runs; equivalent to text below. -/
noncomputable def listedText (tier : Tier) : IProp GF :=
  iprop([∗list] run ∈ Xv6.Generated.KernelMaps.codeRuns,
    [∗list] j ∈ List.range run.length,
      KernelTextDatum.byte capacity era tier (address (run.base + (j : Int))) .discard (value (run.byte j)))

end Xv6.Kernel.KernelTextImage
