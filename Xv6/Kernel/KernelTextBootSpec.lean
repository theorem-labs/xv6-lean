import Xv6.Kernel.KernelTextBootDefs

namespace Xv6.Kernel.KernelTextBoot
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
open Iris.Std.PartialMap

structure PureSpec : Prop where
  lengths : descriptors.map BootWindow.Word.size = [4096,4096,4096,4096,4096,2976,292]
  count : keys.length = 23748
  unique : keys.Nodup
  domain : ∀ pa, pa ∈ keys ↔ ∃ a b, sourceMap a = some b ∧ address a = pa
  bytes : ∀ run ∈ runs, ∀ j, j < run.length →
    nthByte (descriptor run).value j = value (run.byte j)
  ram : ∀ w ∈ descriptors, ∀ j, j < w.size → Tso.AddrIsRAM (addressAdd w.address j)
  source_loaded : ∀ a b, sourceMap a = some b →
    loadedRam Xv6.Machine.bootImage (address a) = some (value b)
  boot_lookup : ∀ (g : State) (memory : Tso.AddressMap Byte), BootFacts Xv6.Machine.bootImage g → FiniteMap.decode memory = g.memory →
    ∀ w ∈ descriptors, ∀ j, j < w.size →
      get? memory (addressAdd w.address j) = some (nthByte w.value j)
  boot_times : ∀ (g : State) (memory : Tso.AddressMap Byte), BootFacts Xv6.Machine.bootImage g → FiniteMap.decode memory = g.memory →
    ∀ w ∈ descriptors, ∀ j, j < w.size →
      get? (Tso.Interp.bootTimestamps memory) (addressAdd w.address j) = some (0, Tso.payNone)
  outside : ∀ {V : Type} (m : Tso.AddressMap V) pa, pa ∉ keys →
    get? (JalBootResources.deleteKeys m keys) pa = get? m pa

/-- All inputs are actual allocator clients and the actual pinned xv6 boot.
The representation equality ties the finite ghost map to that same state;
no independently supplied image-byte or physical-text premise occurs. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  extract : ∀ era g memory diskBytes,
    BootFacts Xv6.Machine.bootImage g → FiniteMap.decode memory = g.memory →
    iprop(Era.bootClients capacity.machine.era era memory g diskBytes ⊢
      rawText capacity era ∗ retained capacity era memory g diskBytes)
  persist : ∀ era,
    iprop(rawText capacity era ⊢ |==> KernelTextImage.physicalText capacity era)
  produce : ∀ era g memory diskBytes,
    BootFacts Xv6.Machine.bootImage g → FiniteMap.decode memory = g.memory →
    iprop(Era.bootClients capacity.machine.era era memory g diskBytes ⊢ |==>
      KernelTextImage.physicalText capacity era ∗ retained capacity era memory g diskBytes)
  allocate : ∀ before template diskBytes,
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      Era.interp capacity.machine.era era g ∗ KernelTextImage.physicalText capacity era ∗
      retained capacity era memory g diskBytes)

end Xv6.Kernel.KernelTextBoot
