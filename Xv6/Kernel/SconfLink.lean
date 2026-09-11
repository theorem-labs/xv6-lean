import Xv6.Kernel.SconfProofs
import Xv6.Kernel.MycpuRegimeShellLink

namespace Xv6.Kernel.Sconf
open Iris MachCSL.Logic

/-- Complete native source configuration component. No instruction proof,
boot allocation, handler contract or replacement resource is assumed. -/
theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity where
  intro := intro_config capacity
  open_parts := open_parts capacity
  close_parts := close_parts capacity
  at_open := at_open capacity
  at_close := at_close capacity
  at_facts := at_facts capacity
  at_sret := at_sret capacity
  at_sie := at_sie capacity
  hardware_access := hardware_access capacity
  interrupts_access := interrupts_access capacity
  environment_access := environment_access capacity
  privilege_agree := privilege_agree capacity
  enable_agree := enable_agree capacity
  environment_agree := environment_agree capacity

theorem registrySpec : Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.Sconf
