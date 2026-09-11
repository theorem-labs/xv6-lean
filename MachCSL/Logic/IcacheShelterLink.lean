import MachCSL.Logic.IcacheShelterProofs
import MachCSL.Logic.LogTxLink

namespace MachCSL.Logic.IcacheShelter

/-- Actual type and transaction cameras in the same existing registry. -/
theorem nativeSpec : Spec LogTx.typeCapacity LogTx.registryCapacity := actual _ _

end MachCSL.Logic.IcacheShelter
