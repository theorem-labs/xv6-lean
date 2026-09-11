import Xv6.Kernel.PushOffCodeDefs
import Xv6.Kernel.MycpuDecodeDefs
import MachCSL.Logic.RegisterPlanDefs

/-! Actual decoder programs and their explicit, source-owned hardware
specialization. Fetch and instruction bodies remain separate. -/
namespace Xv6.Kernel.PushOffDecode
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
abbrev Index := PushOffCode.Index

def program (i : Index) : SailM instruction :=
  if PushOffCode.compressed i then
    ext_decode_compressed (BitVec.ofNat 16 (PushOffCode.encoding i))
  else ext_decode (BitVec.ofNat 32 (PushOffCode.encoding i))

/-- These are the source hardware MISA and source supervisor MENVCFG values,
not zero-register or Machine privilege approximations. -/
def Config (i : Index) (rs : RegisterFile) : Prop :=
  if PushOffCode.compressed i then rs .misa = 0x800000000014112d#64
  else rs .cur_privilege = .Supervisor ∧ rs .menvcfg = 0xa000000000000000#64

structure Shares where
  misa : DFrac
  privilege : DFrac
  environment : DFrac

/-- Every eager repeated read remains in the real program. This is the
set of owned cells, not a claimed list of executed read occurrences. -/
def footprint (shares : Shares) (i : Index) : RegisterFootprint.Footprint :=
  if PushOffCode.compressed i then [(.misa, shares.misa)]
  else [(.cur_privilege, shares.privilege), (.menvcfg, shares.environment)]

/-- Only used to prove finite closed non-JAL certificates. Missing register
values and every memory event are rejected by snapshotPlanRun. -/
def snapshot (i : Index) : JalLoop.Snapshot :=
  if PushOffCode.compressed i then fun r => match r with
    | .misa => some 0x800000000014112d#64
    | _ => none
  else fun r => match r with
    | .cur_privilege => some .Supervisor
    | .menvcfg => some 0xa000000000000000#64
    | _ => none

end Xv6.Kernel.PushOffDecode
