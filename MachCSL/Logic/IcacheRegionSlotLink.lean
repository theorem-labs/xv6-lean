import MachCSL.Logic.IcacheRegionSlotBootProofs
import MachCSL.Logic.IcacheEscrowTokensLink

namespace MachCSL.Logic.IcacheRegionSlot

/-- Same-world native assembly using only already registered component cameras. -/
def nativeCapacity : Capacity IcacheEscrowTokens.registry :=
  ⟨IcacheEscrowTokens.referenceCapacity, IcacheEscrowTokens.couplingCapacity,
    IcacheEscrowTokens.typeCapacity, IcacheEscrowTokens.transactionCapacity,
    IcacheEscrowTokens.recordCapacity, IcacheEscrowTokens.linkCapacity,
    IcacheEscrowTokens.topCapacity, IcacheEscrowTokens.epochCapacity,
    IcacheEscrowTokens.registryCapacity⟩

theorem nativeSpec : Spec nativeCapacity := actual _

end MachCSL.Logic.IcacheRegionSlot
