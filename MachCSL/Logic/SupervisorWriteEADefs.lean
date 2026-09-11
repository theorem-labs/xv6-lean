import MachCSL.Logic.SupervisorMemOuterDefs

namespace MachCSL.Logic.SupervisorWriteEA
open Iris MachCSL.Machine LeanPaperStock.Functions

structure Shares where
  status : DFrac
  privilege : DFrac
  pma : DFrac
  cfg : DFrac
  addr : DFrac

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.mstatus, shares.status), (.cur_privilege, shares.privilege),
    (.pma_regions, shares.pma), (.pmpcfg_n, shares.cfg), (.pmpaddr_n, shares.addr)]

/-- Actual permission conditions; no memory ownership or outcome oracle. -/
structure Config (rs : RegisterFile) (address : BitVec 64) (region : PMA_Region) : Prop where
  privilege : rs .cur_privilege = .Supervisor
  mprv : _get_Mstatus_MPRV (rs .mstatus) = 0#1
  tor : Machine.SupervisorPmp.TorRam rs
  range : SupervisorPhysical.RamRange address 8
  matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region
  writable : (override_PMA region.attributes .PBMT_PMA).writable = true
  aligned : is_aligned_paddr (.Physaddr address) 8 = true

abbrev Result := _root_.Sail.Result Unit (physaddr × ExceptionType)

def program (address : BitVec 64) : SailM Result :=
  mem_write_ea (.Physaddr address) 8 (.Store .Data) .PBMT_PMA false false false

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

end MachCSL.Logic.SupervisorWriteEA
