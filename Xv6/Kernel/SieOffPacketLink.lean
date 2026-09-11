import Xv6.Kernel.SieOffPacketProofs

namespace Xv6.Kernel.SieOffPacket
open Iris

/-- Exact native source-to-shell partition, with no supplied resource law,
execution result or restoration callback. -/
theorem nativeSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity where
  open_packet := open_packet capacity
  close_packet := close_packet capacity
  partition := partition capacity
  certificate := certificate capacity
  boot_pma_from_cell := boot_pma_from_cell capacity

theorem registrySpec {hlc : HasLC} [InvGS_gen hlc MachCSL.Logic.KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.SieOffPacket
