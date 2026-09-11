import Xv6.Kernel.HardwareConfigDefs

namespace Xv6.Kernel.HardwareConfig
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  boot : ∀ counters hpm, Facts (bootValues counters hpm)
  isa : ∀ v, Facts v → v.isa = misaC
  pma : ∀ v, Facts v → PmaClass.allowsAll v.regions

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  persistent : ∀ fixed gen era cpu, Persistent (config capacity fixed gen era cpu)
  counters_persistent : ∀ era cpu, Persistent (counterCaps capacity era cpu)
  persist : ∀ era cpu dq v, iprop(cells capacity era cpu dq v ⊢ |==> cells capacity era cpu .discard v)
  intro : ∀ fixed gen era cpu dq v, Facts v →
    iprop(⊢ cells capacity era cpu dq v -∗ KernelMapStatic.claims capacity era.kernelMap -∗
      MachineInterp.generationCertificate capacity.machine fixed gen era ==∗ config capacity fixed gen era cpu)
  access : ∀ fixed gen era cpu,
    iprop(config capacity fixed gen era cpu ⊢ ∃ v, cells capacity era cpu .discard v ∗ ⌜Facts v⌝ ∗
      KernelMapStatic.claims capacity era.kernelMap ∗
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗ config capacity fixed gen era cpu)
  counters : ∀ fixed gen era cpu, iprop(config capacity fixed gen era cpu ⊢ counterCaps capacity era cpu)
  isa_agree : ∀ fixed gen era cpu dq value,
    iprop(⊢ config capacity fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .misa dq value -∗
      ⌜value = misaC⌝)
  pma_agree : ∀ fixed gen era cpu dq regions,
    iprop(⊢ config capacity fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .pma_regions dq regions -∗
      ⌜PmaClass.allowsAll regions⌝)
  static : ∀ fixed gen era cpu vpn permission, KernelMapStatic.Static vpn permission →
    iprop(config capacity fixed gen era cpu ⊢
      KptGhost.mapAt capacity.ghost era.kernelMap vpn (KernelMapStatic.identityPPN vpn) permission)

end Xv6.Kernel.HardwareConfig
