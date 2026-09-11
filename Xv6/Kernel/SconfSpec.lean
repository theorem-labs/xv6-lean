import Xv6.Kernel.SconfDefs

namespace Xv6.Kernel.Sconf
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  environment_literal : EnvironmentFacts menvcfgS
  delegated_literal : Delegated 0xffff#64
  environment_value : ∀ value, EnvironmentFacts value → value = menvcfgS

/-- Resource assembly/access only, without a supplied execution proof,
CSR transition, physical boot fact or enabled interrupt handler. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  intro : ∀ fixed gen era cpu ms delegation value,
    Delegated delegation → EnvironmentFacts value →
    iprop(⊢ hardware capacity fixed gen era cpu -∗
      cell capacity era cpu .cur_privilege .Supervisor -∗ msOwn capacity era cpu ms -∗
      cell capacity era cpu .mie mieS -∗ cell capacity era cpu .mideleg delegation -∗
      cell capacity era cpu .menvcfg value -∗ sconf capacity fixed gen era cpu)
  open_parts : ∀ fixed gen era cpu,
    iprop(sconf capacity fixed gen era cpu ⊣⊢ ∃ ms, parts capacity fixed gen era cpu ms)
  close_parts : ∀ fixed gen era cpu ms,
    iprop(parts capacity fixed gen era cpu ms ⊢ sconf capacity fixed gen era cpu)
  at_open : ∀ fixed gen era cpu,
    iprop(sconf capacity fixed gen era cpu ⊢ ∃ ms, sconfAt capacity fixed gen era cpu ms)
  at_close : ∀ fixed gen era cpu ms,
    iprop(sconfAt capacity fixed gen era cpu ms ⊢ sconf capacity fixed gen era cpu)
  at_facts : ∀ fixed gen era cpu ms,
    iprop(sconfAt capacity fixed gen era cpu ms ⊢ ⌜SupervisorBits.MsFacts ms⌝)
  at_sret : ∀ fixed gen era cpu ms spp spie,
    iprop(⊢ sconfAt capacity fixed gen era cpu ms -∗
      SupervisorBits.sretBits capacity.supervisorBits (SupervisorBits.namesOfEra era cpu) spp spie -∗
      ⌜_get_Mstatus_SPP ms = spp ∧ _get_Mstatus_SPIE ms = spie⌝)
  at_sie : ∀ fixed gen era cpu ms q value,
    iprop(⊢ sconfAt capacity fixed gen era cpu ms -∗
      SupervisorBits.bit capacity.supervisorBits (SupervisorBits.namesOfEra era cpu).sie q value -∗
      ⌜_get_Mstatus_SIE ms = value⌝)
  hardware_access : ∀ fixed gen era cpu,
    iprop(sconf capacity fixed gen era cpu ⊢
      hardware capacity fixed gen era cpu ∗ sconf capacity fixed gen era cpu)
  interrupts_access : ∀ fixed gen era cpu,
    iprop(sconf capacity fixed gen era cpu ⊢ ∃ delegation,
      cell capacity era cpu .mie mieS ∗ cell capacity era cpu .mideleg delegation ∗
      ⌜Delegated delegation⌝ ∗
      (cell capacity era cpu .mie mieS -∗ cell capacity era cpu .mideleg delegation -∗
        sconf capacity fixed gen era cpu))
  environment_access : ∀ fixed gen era cpu,
    iprop(sconf capacity fixed gen era cpu ⊢ ∃ value,
      cell capacity era cpu .menvcfg value ∗ ⌜EnvironmentFacts value⌝ ∗
      (cell capacity era cpu .menvcfg value -∗ sconf capacity fixed gen era cpu))
  privilege_agree : ∀ fixed gen era cpu dq value,
    iprop(⊢ sconf capacity fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .cur_privilege dq value -∗
      ⌜value = .Supervisor⌝)
  enable_agree : ∀ fixed gen era cpu dq value,
    iprop(⊢ sconf capacity fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mie dq value -∗ ⌜value = mieS⌝)
  environment_agree : ∀ fixed gen era cpu dq value,
    iprop(⊢ sconf capacity fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .menvcfg dq value -∗
      ⌜EnvironmentFacts value⌝)

end Xv6.Kernel.Sconf
