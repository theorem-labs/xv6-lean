import MachCSL.Logic.SpinlockBootHandlerProofs
import MachCSL.Logic.UartWPLink
import MachCSL.Logic.PlicWPLink
import MachCSL.Logic.ResetDiskWPProofs

namespace MachCSL.Logic.SpinlockBootHandler
open Iris Iris.BI MachCSL.Machine

theorem registry_boot_handler [Platform] {hlc : HasLC} [InvGS_gen hlc FsTop.registry]
    (ns : JalBootHandler.Namespaces) (N : Namespace) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (template : Era.Record) :
    iprop(⊢ ObservationInvariant.trivial FsTop.machineCapacity.power ns.observations fixed.observations -∗
      PowerWP.bootHandler FsTop.machineCapacity SpinlockImage.image fixed whole template) :=
  boot_handler FsTop.machineCapacity FsTop.uartCapacity ns FsTop.lockCapacity N
    (UartWP.uartWPSpec FsTop.machineCapacity FsTop.uartCapacity)
    (PlicWP.plicWPSpec FsTop.machineCapacity)
    (ResetDiskWP.resetDiskWPSpec FsTop.machineCapacity) fixed whole template

end MachCSL.Logic.SpinlockBootHandler
