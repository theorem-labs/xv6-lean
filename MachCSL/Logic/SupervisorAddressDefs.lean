import MachCSL.Logic.SupervisorMemOuterDefs

namespace MachCSL.Logic.SupervisorAddress
open Iris MachCSL.Machine LeanPaperStock.Functions

inductive Kind where | load | store
  deriving DecidableEq

def access : Kind → MemoryAccessType mem_payload
  | .load => .Load .Data
  | .store => .Store .Data

structure Shares where
  status : DFrac
  privilege : DFrac
  envcfg : DFrac
  satp : DFrac

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.mstatus, shares.status), (.cur_privilege, shares.privilege),
    (.menvcfg, shares.envcfg), (.satp, shares.satp)]

structure Config (rs : RegisterFile) (mode : SATPMode) : Prop where
  privilege : rs .cur_privilege = .Supervisor
  mprv : _get_Mstatus_MPRV (rs .mstatus) = 0#1
  mxr : _get_Mstatus_MXR (rs .mstatus) = 0#1
  pmm : pmm_mode_backwards (_get_MEnvcfg_PMM (rs .menvcfg)) = .PMM_Disabled
  sxl : _get_Mstatus_SXL (rs .mstatus) = 2#2
  decoded : satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 (rs .satp))) = some mode

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

def program (address : BitVec 64) (kind : Kind) : SailM virtaddr :=
  transform_effective_address (.Virtaddr address) (access kind)

end MachCSL.Logic.SupervisorAddress
