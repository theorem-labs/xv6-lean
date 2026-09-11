import MachCSL.Logic.EventWPCode
import MachCSL.Logic.PlicWPDefs

namespace MachCSL.Logic.JalBootResources
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors}

def cpuRegisters (capacity : Registers.Capacity GF) (names : GlobalRegisters.Names)
    (files : CPU → RegisterFile) : IProp GF :=
  iprop([∗set] cpu ∈ GlobalRegisters.allCPUs, EventWP.ownedCells capacity (names cpu) (files cpu))

def cpuReservations (capacity : Reservations.Capacity GF) (γ : GName)
    (values : CPU → Reservations.Value) : IProp GF :=
  iprop([∗set] cpu ∈ GlobalRegisters.allCPUs, Reservations.resvFrag capacity γ cpu (values cpu))

end MachCSL.Logic.JalBootResources
