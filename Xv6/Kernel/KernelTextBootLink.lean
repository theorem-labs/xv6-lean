import Xv6.Kernel.KernelTextBootSharing
import MachCSL.Logic.EraLink

namespace Xv6.Kernel.KernelTextBoot
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- The actual native era allocator supplies both maps exactly once. The
exhaustive finite-map witness is used solely through decode_encodeAll. -/
theorem allocate (before : State) (template : Era.Record) (diskBytes : Nat) :
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      Era.interp capacity.machine.era era g ∗ KernelTextImage.physicalText capacity era ∗
      retained capacity era memory g diskBytes) := by
  dsimp only
  let g := Xv6.Machine.boot before
  let memory := FiniteMap.encodeAll g.memory
  have facts := Xv6.Machine.boot_facts before
  have decoded : FiniteMap.decode memory = g.memory := FiniteMap.decode_encodeAll _
  imod Era.allocate capacity.machine.era (Era.contracts capacity.machine.era)
    Xv6.Machine.bootImage g memory template diskBytes facts decoded with ⟨%era, %same, Hinterp, Hclients⟩
  imod produce_update capacity era g memory diskBytes facts decoded $$ Hclients with ⟨Htext, Hretained⟩
  imodintro
  iexists era
  iframe
  ipureintro
  exact same

/-- Every boot, carve and persistence field is discharged by actual native
resources and the pinned kernel image; no caller component law is needed. -/
theorem nativeSpec : Spec capacity where
  extract := extract capacity
  persist := persist capacity
  produce := produce capacity
  allocate := allocate capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec _

end Xv6.Kernel.KernelTextBoot
