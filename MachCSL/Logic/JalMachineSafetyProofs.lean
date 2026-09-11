import MachCSL.Logic.JalMachineSafetyDefs
import MachCSL.Logic.MachineAdequacyLink

namespace MachCSL.Logic.JalMachineSafety
open Iris Iris.BI MachCSL.Machine

theorem initialState_conditions (devices : Devices.State) :
    (initialState devices).power = false ∧ (initialState devices).generation = 0 :=
  ⟨rfl, rfl⟩

/-- Application linkage consumes the boot handler in the very native world
provided by adequacy. The final link file discharges this premise. -/
theorem initializer_of_boot_handler [Platform] (initial : State) (diskBytes : Nat)
    (handler : ∀ [InvGS UartGhost.registry]
      (fixed : MachineInterp.FixedNames) (whole : List Observation),
      iprop(⊢ ObservationInvariant.trivial UartGhost.machineCapacity.power
        namespaces.observations fixed.observations -∗
        PowerWP.bootHandler UartGhost.machineCapacity jalImage fixed whole template)) :
    MachineAdequacy.BootInitializer UartGhost.machineCapacity jalImage initial
      diskBytes template namespaces.observations :=
  MachineAdequacy.initializer_of_handler UartGhost.machineCapacity jalImage initial
    diskBytes template namespaces.observations handler

end MachCSL.Logic.JalMachineSafety
