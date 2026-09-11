import MachCSL.Logic.IcacheSlotCouplingProofs
import MachCSL.Logic.IcacheRefLedgerLink

namespace MachCSL.Logic.IcacheSlotCoupling

/-- Existing slots 28–31 suffice. No camera or ghost name is allocated here. -/
theorem nativeSpec : Spec IcacheRefLedger.registryCapacity IcacheRefLedger.couplingCapacity :=
  actual _ _

end MachCSL.Logic.IcacheSlotCoupling
