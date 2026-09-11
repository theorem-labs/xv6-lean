import MachCSL.Logic.RegisterPlanDefs

namespace MachCSL.Machine.SupervisorBare
open LeanPaperStock.Functions Iris

/-- Exact bounded family of source `SRegime.s_acc_ok` (line 182). -/
inductive Supported : MemoryAccessType mem_payload → Prop
  | fetch : Supported (.InstructionFetch ())
  | load : Supported (.Load .Data)
  | store : Supported (.Store .Data)
  | swap (acquire release : Bool) : Supported (.Atomic (.AMOSWAP, acquire, release, .Data, .Data))

/-- Actual sufficient Bare/supervisor fields; ASID, PPN and all other fields are arbitrary. -/
structure Config (rs : RegisterFile) : Prop where
  privilege : rs .cur_privilege = .Supervisor
  sxl : _get_Mstatus_SXL (rs .mstatus) = 2#2
  mode : _get_Satp64_Mode (Mk_Satp64 (rs .satp)) = 0#4

/-- Fetch ignores MPRV. The other supported calls use the source MPRV-zero fact. -/
def Effective (rs : RegisterFile) (access : MemoryAccessType mem_payload) : Prop :=
  access = .InstructionFetch () ∨ _get_Mstatus_MPRV (rs .mstatus) = 0#1

structure Shares where
  status : DFrac
  privilege : DFrac
  satp : DFrac

def footprint (shares : Shares) : MachCSL.Logic.RegisterFootprint.Footprint :=
  [(.mstatus, shares.status), (.cur_privilege, shares.privilege), (.satp, shares.satp)]

end MachCSL.Machine.SupervisorBare
