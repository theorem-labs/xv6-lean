import MachCSL.Logic.InvariantProofs
import MachCSL.Logic.InvariantRegistry

namespace MachCSL.Logic.Invariant

theorem registryInvariantSpec : InvariantSpec registryCapacity := invariantSpec registryCapacity

@[reducible] def registryMachineGS [Platform] (names : Names) (image : Machine.BootImage)
    (fixed : MachineInterp.FixedNames) (whole : List Machine.Observation) :=
  machineGS registryCapacity machineCapacity names image fixed whole

end MachCSL.Logic.Invariant
