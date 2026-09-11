import Xv6.Kernel.MycpuBootResourcesDefs

namespace Xv6.Kernel.MycpuBootResources
open Iris Iris.BI MachCSL.Memory MachCSL.Machine MachCSL.Logic

/-- Physical slice contracts; no translation, execution, or mapping oracle. -/
structure Spec {GF : BundledGFunctors} (capacity : Era.Capacity GF) : Prop where
  extract : ∀ era g memory diskBytes,
    BootFacts Xv6.Machine.bootImage g → FiniteMap.decode memory = g.memory →
    iprop(Era.bootClients capacity era memory g diskBytes ⊢
      rawSpan (storeCapacity capacity) (storeNames era) ∗
      remainder (storeCapacity capacity) (storeNames era) memory ∗
      Tso.Views.natLB capacity.views era.logLength 0 ∗ otherClients capacity era memory g diskBytes)
  allocate : ∀ before template diskBytes,
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      Era.interp capacity era g ∗
      rawSpan (storeCapacity capacity) (storeNames era) ∗
      remainder (storeCapacity capacity) (storeNames era) memory ∗
      Tso.Views.natLB capacity.views era.logLength 0 ∗ otherClients capacity era memory g diskBytes)
  access : ∀ era ξ dq i,
    iprop(contextSpan (storeCapacity capacity) (storeNames era) ξ dq ⊢
      fetchWindow (storeCapacity capacity) (storeNames era) ξ dq i ∗
      (fetchWindow (storeCapacity capacity) (storeNames era) ξ dq i -∗
        contextSpan (storeCapacity capacity) (storeNames era) ξ dq))
  share : ∀ era,
    iprop(rawSpan (storeCapacity capacity) (storeNames era) ⊢ |==>
      physicalSpan (storeCapacity capacity) (storeNames era) .discard)
  windows : ∀ era ξ,
    iprop(physicalSpan (storeCapacity capacity) (storeNames era) .discard ⊢
      physicalSpan (storeCapacity capacity) (storeNames era) .discard ∗
      fetchWindows (storeCapacity capacity) (storeNames era) ξ)

end Xv6.Kernel.MycpuBootResources
