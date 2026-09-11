import MachCSL.Logic.SupervisorBareFetchDefs

namespace MachCSL.Logic.SupervisorBareWrite
open Iris MachCSL.Machine LeanPaperStock.Functions

abbrev Shares := SupervisorBareFetch.Shares
abbrev footprint := SupervisorBareFetch.footprint
abbrev cells := @SupervisorBareFetch.cells

def physical (shares : Shares) : SupervisorWrite.Shares :=
  ⟨shares.physical.pma, shares.physical.cfg, shares.physical.addr, shares.physical.htif⟩

structure Config (rs : RegisterFile) (address : BitVec 64) (region : PMA_Region) : Prop where
  bare : SupervisorBare.Config rs
  mprv : _get_Mstatus_MPRV (rs .mstatus) = 0#1
  tor : SupervisorPmp.TorRam rs
  range : SupervisorPhysical.RamRange address 8
  disabled : rs .htif_tohost_base = none
  matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region
  writable : (override_PMA region.attributes .PBMT_PMA).writable = true

abbrev Result := _root_.Sail.Result Bool ExecutionResult

def program [Platform] (address word : BitVec 64) : SailM Result :=
  vmem_write_addr (.Virtaddr address) 8 word (.Store .Data) false false false

end MachCSL.Logic.SupervisorBareWrite
