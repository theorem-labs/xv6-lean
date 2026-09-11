import MachCSL.Logic.SupervisorWriteDefs
import MachCSL.Logic.TsoPinnedWriteWPDefs
import LeanPaperStock.Vmem

/-! The actual explicit-supervisor conditional PTE write wrapper. Its four
fractional register cells cover PMA, PMP arrays and the eager HTIF check. -/
namespace MachCSL.Logic.SupervisorPteWrite
open Iris MachCSL.Machine LeanPaperStock.Functions

abbrev Shares := SupervisorWrite.Shares
abbrev footprint := SupervisorWrite.footprint
abbrev cells := @SupervisorWrite.cells
abbrev Result := SupervisorWrite.Result
abbrev request := TsoPinnedWriteWP.conditionalRequest

def checked (address word : BitVec 64) : SailM Result :=
  checked_mem_write (.Physaddr address) 8 word (.Store .PageTableEntry)
    .PBMT_PMA .Supervisor () false false true

def program (address word : BitVec 64) : SailM Result :=
  mem_write_value_priv (.Physaddr address) 8 word .Supervisor (.Store .PageTableEntry)
    .PBMT_PMA false false true

structure Config (rs : RegisterFile) (address : BitVec 64) (region : PMA_Region) : Prop where
  tor : SupervisorPmp.TorRam rs
  range : SupervisorPhysical.RamRange address 8
  disabled : rs .htif_tohost_base = none
  matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region
  grant : (override_PMA region.attributes .PBMT_PMA).supports_pte_write = true
  aligned : is_aligned_paddr (.Physaddr address) 8 = true

/-- The checked prefix keeps every optional successful raw result and its
actual error-to-false tail. Fault routes are discharged by the concrete plan. -/
def OneWrite (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (address word : BitVec 64) (program : SailM α) (value : Bool → α) : Prop :=
  ∃ tail, SupervisorWrite.Boundary fp rs (request address word) program tail ∧
    (∀ result, tail (.Ok result) = pure (value true)) ∧
    tail (.Err ()) = pure (value false)

end MachCSL.Logic.SupervisorPteWrite
