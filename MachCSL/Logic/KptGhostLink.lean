import MachCSL.Logic.KptGhostProofs
import MachCSL.Logic.KptGhostRegistry

namespace MachCSL.Logic.KptGhost
open Iris

/-- Generic native implementation for supplied, coherent camera witnesses. -/
theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

/-- No caller-supplied algebra laws remain at the shared 48-slot family. -/
theorem registrySpec : Spec kptCapacity := nativeSpec kptCapacity

theorem era_map_name (era : Era.Record) : (Names.ofEra era).mapping = era.kernelMap := rfl
theorem era_tree_name (era : Era.Record) : (Names.ofEra era).tree = era.kernelPageTable := rfl
theorem era_bound_name (era : Era.Record) : (Names.ofEra era).bound = era.kernelPageTableBound := rfl
theorem era_log_name (era : Era.Record) : (Names.ofEra era).logLength = era.logLength := rfl

/-- The receipt is exactly the existing machine-era Views assertion. -/
theorem registry_bound (γ logName : GName) (B : Nat) :
    bound kptCapacity γ logName B = iprop(iOwn (E := boundSlot) γ (boundShot B) ∗
      Tso.Views.llb machineCapacity.era.views logName B) := rfl

end MachCSL.Logic.KptGhost
