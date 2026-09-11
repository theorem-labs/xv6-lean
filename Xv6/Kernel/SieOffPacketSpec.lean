import Xv6.Kernel.SieOffPacketDefs

namespace Xv6.Kernel.SieOffPacket
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

/-- Exact resource partition/restoration. No successful instruction, full
state equality, boot PMA equality or caller restoration callback is assumed. -/
structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  open_packet : ∀ fixed gen era cpu tier ξ file available pc,
    iprop(input capacity fixed gen era cpu tier ξ file available pc ⊢ ∃ regime control,
      ⌜Ambient pc control⌝ ∗ ⌜MycpuRegimeShell.Admits regime.shell tier⌝ ∗
      opened capacity fixed gen era cpu tier ξ file available regime control)
  close_packet : ∀ fixed gen era cpu tier ξ file available pc regime control,
    Boundary pc control →
    iprop(opened capacity fixed gen era cpu tier ξ file available regime control ⊢
      input capacity fixed gen era cpu tier ξ file available pc)
  partition : ∀ fixed gen era cpu tier ξ file available regime control,
    iprop(opened capacity fixed gen era cpu tier ξ file available regime control ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (MycpuRegimeShell.entry control cpu file) (MycpuRegimeShell.footprint MycpuRegimeShell.sourceShares) ∗
      MycpuRegimeShell.bitFrame capacity era cpu (control .mstatus) ∗ ⌜file 0#5 = 0#64⌝ ∗
      MycpuRegimeShell.translation capacity era cpu regime.shell ∗
      frame capacity fixed gen era cpu tier ξ file available regime ∗
      Reservations.resvAny capacity.machine.era.reservations era.reservations cpu)
  certificate : ∀ fixed gen era cpu tier ξ file available regime control,
    iprop(opened capacity fixed gen era cpu tier ξ file available regime control ⊢
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      opened capacity fixed gen era cpu tier ξ file available regime control)
  boot_pma_from_cell : ∀ fixed gen era cpu tier ξ file available regime control,
    iprop(⊢ opened capacity fixed gen era cpu tier ξ file available regime control -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .pma_regions .discard pmaBoot -∗
      ⌜control .pma_regions = pmaBoot⌝ ∗
      opened capacity fixed gen era cpu tier ξ file available regime control)

end Xv6.Kernel.SieOffPacket
