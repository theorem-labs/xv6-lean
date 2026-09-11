import Xv6.Kernel.BootPmaProofs

namespace Xv6.Kernel.BootPma
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- One actual era/text allocation; consume only its remaining PMA cells. -/
theorem allocate_text (before : State) (template : Era.Record) (diskBytes : Nat) :
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      Era.interp capacity.machine.era era g ∗ KernelTextImage.physicalText capacity era ∗
      all capacity era ∗ textRetained capacity era memory g diskBytes) := by
  dsimp only
  imod KernelTextBoot.allocate capacity before template diskBytes with ⟨%era, %same, Hi, Htext, Hr⟩
  imod produce_text_retained capacity Xv6.Machine.bootImage era (Xv6.Machine.boot before)
    (FiniteMap.encodeAll (Xv6.Machine.boot before).memory) diskBytes
    (Xv6.Machine.boot_facts before) $$ Hr with ⟨Hp, Hr⟩
  imodintro
  iexists era
  iframe
  ipureintro
  exact same

/-- Closed native component contracts: no caller register-law or producer premise. -/
theorem nativeSpec : Spec capacity where
  partition_hart := partition_hart capacity
  partition_all := partition_all capacity
  persist_all := persist_all capacity
  at_cpu := at_cpu capacity
  produce := produce capacity
  produce_text_retained := produce_text_retained capacity
  produce_text := produce_text capacity
  allocate_text := allocate_text capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec _

end Xv6.Kernel.BootPma
