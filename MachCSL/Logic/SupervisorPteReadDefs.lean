import MachCSL.Logic.SupervisorReadDefs
import MachCSL.Logic.TsoPinnedReadWPDefs
import LeanPaperStock.Vmem

namespace MachCSL.Logic.SupervisorPteRead
open Iris MachCSL.Machine LeanPaperStock.Functions

abbrev Shares := SupervisorRead.Shares
abbrev footprint := SupervisorRead.footprint
abbrev cells := @SupervisorRead.cells
abbrev Result := _root_.Sail.Result (BitVec 64) (physaddr × ExceptionType)
abbrev CheckedResult := SupervisorRead.Result

def kind (reserved : Bool) : read_kind := if reserved then .Read_RISCV_reserved else .Read_plain

def request (reserved : Bool) (address : BitVec 64) : MemoryReadWP.ReadRequest 8 :=
  { access_kind := .AK_explicit { variety := (if reserved then .AV_exclusive else .AV_plain), strength := .AS_normal }
    va := none, pa := address, translation := (), size := 8, tag := false }

def checked (reserved : Bool) (address : BitVec 64) : SailM CheckedResult :=
  checked_mem_read (.Load .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr address) 8
    false false reserved false

def program (reserved : Bool) (address : BitVec 64) : SailM Result :=
  mem_read_priv (.Load .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr address) 8 false false reserved

structure Config (rs : RegisterFile) (address : BitVec 64) (region : PMA_Region) : Prop where
  tor : SupervisorPmp.TorRam rs
  range : SupervisorPhysical.RamRange address 8
  disabled : rs .htif_tohost_base = none
  matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region
  grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (.Load .PageTableEntry)
  aligned : is_aligned_paddr (.Physaddr address) 8 = true

def OneRead (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (reserved : Bool)
    (address : BitVec 64) (program : SailM α) (value : BitVec 64 → α) : Prop :=
  ∃ tail, SupervisorRead.Boundary fp rs (request reserved address) program tail ∧
    (∀ word tag, tail (.Ok (word, tag)) = pure (value word)) ∧
    tail (.Err ()) = _root_.Sail.ConcurrencyInterfaceV1.Free.fail .Exit

end MachCSL.Logic.SupervisorPteRead
