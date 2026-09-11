import Xv6.Kernel.BootPmaDefs

namespace Xv6.Kernel.BootPma
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  keys_count : remainingKeys.length = 179
  keys_unique : remainingKeys.Nodup
  keys_mem : ∀ r, r ∈ remainingKeys ↔ r ≠ .pma_regions
  remainder_lookup : ∀ rs r, Iris.Std.PartialMap.get? (remainingMap rs) r =
    if r = .pma_regions then none else some (⟨r,rs r⟩ : Registers.Value)
  boot_pma : ∀ image g, BootFacts image g → ∀ cpu, g.registers cpu .pma_regions = pmaBoot

/-- Persistence consumes the extracted full fragments. No full PMA cell is
returned in any remainder. Combined text production allocates/carves once. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  partition_hart : ∀ name rs,
    iprop(Registers.initialCells capacity.machine.era.registers name rs ⊣⊢
      Registers.regPointsto capacity.machine.era.registers name .pma_regions (.own 1) (rs .pma_regions) ∗
      remainingHart capacity name rs)
  partition_all : ∀ era files,
    iprop(GlobalRegisters.allInitialCells capacity.machine.era.registers era.registers files ⊣⊢
      raw capacity era files ∗ remainingRegisters capacity era files)
  persist_all : ∀ era files, (∀ cpu, files cpu .pma_regions = pmaBoot) →
    iprop(raw capacity era files ⊢ |==> all capacity era)
  at_cpu : ∀ era cpu, iprop(all capacity era ⊢ cell capacity era cpu ∗ all capacity era)
  produce : ∀ image era g memory diskBytes, BootFacts image g →
    iprop(Era.bootClients capacity.machine.era era memory g diskBytes ⊢ |==>
      (all capacity era ∗ retained capacity era memory g diskBytes))
  produce_text_retained : ∀ image era g memory diskBytes, BootFacts image g →
    iprop(KernelTextBoot.retained capacity era memory g diskBytes ⊢ |==>
      (all capacity era ∗ textRetained capacity era memory g diskBytes))
  produce_text : ∀ era g memory diskBytes,
    BootFacts Xv6.Machine.bootImage g → FiniteMap.decode memory = g.memory →
    iprop(Era.bootClients capacity.machine.era era memory g diskBytes ⊢ |==>
      (KernelTextImage.physicalText capacity era ∗ all capacity era ∗
        textRetained capacity era memory g diskBytes))
  allocate_text : ∀ before template diskBytes,
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      Era.interp capacity.machine.era era g ∗ KernelTextImage.physicalText capacity era ∗
      all capacity era ∗ textRetained capacity era memory g diskBytes)

end Xv6.Kernel.BootPma
