import Xv6.Kernel.KernelTextBootMapDefs

namespace Xv6.Kernel.KernelTextBootMap
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  install_name : ∀ template name, (install template name).kernelMap = name
  install_other : ∀ template name, OtherAuxiliarySame (install template name) template
  auxiliary_iff : ∀ era template name,
    Era.AuxiliarySame era (install template name) ↔
      era.kernelMap = name ∧ OtherAuxiliarySame era template
  installed : ∀ era template name memory,
    era.image = memory → Era.AuxiliarySame era (install template name) → Installed era template name memory

/-- Combined actual native allocation; no supplied ghost authority, name
agreement, image-byte correctness or physical-tree predicate is an input. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
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

end Xv6.Kernel.KernelTextBootMap
