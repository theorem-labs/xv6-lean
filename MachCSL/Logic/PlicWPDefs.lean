import MachCSL.Logic.UartWPDefs

/-! Source `WpUart.v:wire_inv,wp_plic_loop`: complete existential custody of
both hardware interrupt pins on all eight harts. -/
namespace MachCSL.Logic.PlicWP
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors}

def wireCells (capacity : Registers.Capacity GF) (names : GlobalRegisters.Names)
    (seip meip : CPU → BitVec 1) : IProp GF :=
  iprop([∗set] cpu ∈ GlobalRegisters.allCPUs,
    Registers.regPointsto capacity (names cpu) .sig_seip (.own 1) (seip cpu) ∗
    Registers.regPointsto capacity (names cpu) .sig_meip (.own 1) (meip cpu))

def wireBody (capacity : Registers.Capacity GF) (names : GlobalRegisters.Names) : IProp GF :=
  iprop(∃ seip meip : CPU → BitVec 1, wireCells capacity names seip meip)

def wireInv {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Registers.Capacity GF)
    (N : Namespace) (names : GlobalRegisters.Names) : IProp GF := inv N (wireBody capacity names)

end MachCSL.Logic.PlicWP
