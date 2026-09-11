import Xv6.Kernel.KptSharedDefs
import Xv6.Kernel.KptMissDefs

/-! Derive each walk/update configuration from actual owned-slot geometry
and the source's ambient RAM PMP/PMA/HTIF configuration. -/
namespace Xv6.Kernel.KptHardware
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptShared.Capacity

structure Controls (rs : RegisterFile) : Prop where
  tor : SupervisorPmp.TorRam rs
  htif : rs .htif_tohost_base = none
  pma : rs .pma_regions = pmaBoot

def ramRegion : PMA_Region :=
  ⟨BitVec.ofNat 64 ramLow, BitVec.ofNat 64 (ramHigh - ramLow), pmaBootRam, true⟩

def regions : Nat → PMA_Region := fun _ => ramRegion

end Xv6.Kernel.KptHardware
