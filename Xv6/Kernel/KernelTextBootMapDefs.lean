import Xv6.Kernel.KernelTextBootDefs

/-! Fresh static-map allocation installed in the actual boot-era record.
Only its runtime kernelMap field is replaced in the caller's template.
No physical page-table, translation receipt or supervisor state is installed. -/
namespace Xv6.Kernel.KernelTextBootMap
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KernelTextBoot.Capacity

def install (template : Era.Record) (name : GName) : Era.Record :=
  { template with kernelMap := name }

/-- Exactly the remaining ten source auxiliary fields. Machine-era names
are genuinely freshly allocated and are not claimed equal to the template. -/
def OtherAuxiliarySame (era template : Era.Record) : Prop :=
  era.kernelPageTable = template.kernelPageTable ∧
  era.kernelPageTableBound = template.kernelPageTableBound ∧
  era.supervisorTranslation = template.supervisorTranslation ∧
  era.supervisorInterruptEnable = template.supervisorInterruptEnable ∧
  era.supervisorPreviousPrivilege = template.supervisorPreviousPrivilege ∧
  era.supervisorPreviousInterruptEnable = template.supervisorPreviousInterruptEnable ∧
  era.parkedHart = template.parkedHart ∧ era.processState = template.processState ∧
  era.logMirror = template.logMirror ∧ era.heldLocks = template.heldLocks

/-- Output fact paid by the two native allocators and the record update;
it is never an input hypothesis to the combined producer. -/
def Installed (era template : Era.Record) (name : GName) (memory : Tso.AddressMap Byte) : Prop :=
  era.image = memory ∧ era.kernelMap = name ∧ OtherAuxiliarySame era template

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Map resources use the actual era name. Physical and identity text are
both persistent; the map authority remains linear and is returned whole. -/
noncomputable def resources (era : Era.Record) (memory : Tso.AddressMap Byte)
    (g : State) (diskBytes : Nat) : IProp GF :=
  iprop(Era.interp capacity.machine.era era g ∗
    KernelMapStatic.authority capacity era.kernelMap ∗ KernelMapStatic.claims capacity era.kernelMap ∗
    KernelTextImage.physicalText capacity era ∗ KernelTextImage.text capacity era .identity ∗
    KernelTextBoot.retained capacity era memory g diskBytes)

end Xv6.Kernel.KernelTextBootMap
