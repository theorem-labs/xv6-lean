import Xv6.Kernel.BootTextPmaMapDefs

namespace Xv6.Kernel.BootTextPmaMap
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- Native composition at the actual same era. The installed-name fact is
an allocation result, never a caller-supplied agreement or authority. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  produce : ∀ image era g memory diskBytes, BootFacts image g →
    iprop(KernelTextBootMap.resources capacity era memory g diskBytes ⊢ |==>
      resources capacity era memory g diskBytes)
  allocate : ∀ before template diskBytes,
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ name era, ⌜Installed era template name memory⌝ ∗
      resources capacity era memory g diskBytes)
  allocate_frame : ∀ before template diskBytes (frame : IProp GF),
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(frame ⊢ |==> ∃ name era, ⌜Installed era template name memory⌝ ∗
      resources capacity era memory g diskBytes ∗ frame)

end Xv6.Kernel.BootTextPmaMap
