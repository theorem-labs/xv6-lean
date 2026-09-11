import Xv6.Kernel.MycpuDecodeProofs
import MachCSL.Logic.RegisterPlanDefs

namespace Xv6.Kernel.MycpuReturn
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- Source RiscvExtras.ret_pc, with modular 64-bit addressing. -/
def retPC (ra : BitVec 64) : BitVec 64 := _root_.Sail.BitVec.update ra 0 0#1

structure Shares where
  ra : Iris.DFrac
  privilege : Iris.DFrac
  menvcfg : Iris.DFrac
  misa : Iris.DFrac

/-- Source control shares; the singleton RA cell replaces the unused GPR remainder. -/
def sourceShares : Shares := ⟨.own 1, .own 1, .own 1, .discard⟩

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.nextPC, .own 1), (.x1, shares.ra), (.cur_privilege, shares.privilege),
    (.menvcfg, shares.menvcfg), (.misa, shares.misa)]

def pcFootprint (shares : Shares) (pcShare : Iris.DFrac) : RegisterFootprint.Footprint :=
  (.PC, pcShare) :: footprint shares

structure Config (rs : RegisterFile) : Prop where
  privilege : rs .cur_privilege = .Supervisor
  lpe : bool_bit_backwards (_get_MEnvcfg_LPE (rs .menvcfg)) = false
  compressed : _get_Misa_C (rs .misa) = 1#1

structure SourceConfig (rs : RegisterFile) : Prop where
  privilege : rs .cur_privilege = .Supervisor
  menvcfg : rs .menvcfg = 0xa000000000000000#64
  misa : rs .misa = 0x800000000014112d#64

def after (rs : RegisterFile) : RegisterFile :=
  MachCSL.Sail.Registers.write rs .nextPC (retPC (rs .x1))

/-- The actual compressed execute/ExecuteAs selection, before retirement. -/
def body [Platform] : SailM ExecutionResult := do
  match ← execute (MycpuDecode.decoded ⟨13, by decide⟩) with
  | .ExecuteAs other => execute other
  | result => pure result

end Xv6.Kernel.MycpuReturn
