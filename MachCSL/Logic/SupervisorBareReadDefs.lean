import MachCSL.Logic.SupervisorBareFetchDefs

namespace MachCSL.Logic.SupervisorBareRead
open Iris MachCSL.Machine LeanPaperStock.Functions

abbrev Shares := SupervisorBareFetch.Shares
abbrev footprint := SupervisorBareFetch.footprint
abbrev cells := @SupervisorBareFetch.cells

def physical (shares : Shares) : SupervisorRead.Shares :=
  ⟨shares.physical.pma, shares.physical.cfg, shares.physical.addr, shares.physical.htif⟩

structure Config (rs : RegisterFile) (address : BitVec 64) (region : PMA_Region) : Prop where
  bare : SupervisorBare.Config rs
  mprv : _get_Mstatus_MPRV (rs .mstatus) = 0#1
  tor : SupervisorPmp.TorRam rs
  range : SupervisorPhysical.RamRange address 8
  disabled : rs .htif_tohost_base = none
  matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region
  readable : (override_PMA region.attributes .PBMT_PMA).readable = true

abbrev Result := _root_.Sail.Result (BitVec 64) ExecutionResult

def program (address : BitVec 64) : SailM Result :=
  vmem_read_addr (.Virtaddr address) 8 (.Load .Data) false false false

end MachCSL.Logic.SupervisorBareRead
