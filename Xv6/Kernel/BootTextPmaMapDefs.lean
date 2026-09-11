import Xv6.Kernel.KernelTextBootMapDefs
import Xv6.Kernel.BootPmaDefs

/-! Combined actual static-map, sparse text and PMA boot clients. The PMA
producer consumes the register column of the same allocated era. -/
namespace Xv6.Kernel.BootTextPmaMap
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KernelTextBootMap.Capacity
abbrev Installed := KernelTextBootMap.Installed

/-- All original outputs, with the eight full PMA cells consumed exactly
once. Authority is linear; claims, both text predicates and PMA are persistent. -/
noncomputable def resources {GF : BundledGFunctors} (capacity : Capacity GF)
    (era : Era.Record) (memory : Tso.AddressMap Byte) (g : State) (diskBytes : Nat) : IProp GF :=
  iprop(Era.interp capacity.machine.era era g ∗
    KernelMapStatic.authority capacity era.kernelMap ∗ KernelMapStatic.claims capacity era.kernelMap ∗
    KernelTextImage.physicalText capacity era ∗ KernelTextImage.text capacity era .identity ∗
    BootPma.all capacity era ∗ BootPma.textRetained capacity era memory g diskBytes)

end Xv6.Kernel.BootTextPmaMap
