import Xv6.Kernel.MycpuBareDefs
import Xv6.Kernel.HartTpDefs
import MachCSL.Logic.SupervisorBitsDefs

/-! Disabled Bare mycpu resource adapter. One full pinned GPR bundle and
one full mstatus cell fund the actual cycle footprint; no paired duplicate
28-cell assertion is an input. This is not the full source sie_cap_gpr. -/
namespace Xv6.Kernel.MycpuOff
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure Capacity (GF : BundledGFunctors) where
  machine : MachineInterp.Capacity GF
  bits : GhostVarG GF (BitVec 1)

def Capacity.supervisorBits {GF : BundledGFunctors} (capacity : Capacity GF) :
    SupervisorBits.Capacity GF := ⟨capacity.machine.era.registers, capacity.bits⟩

/-- Only the independently supplied control-register shares. Both mstatus
and all GPR cells come from full source ownership, not share parameters. -/
structure Shares where
  privilege : DFrac
  satp : DFrac
  physical : SupervisorFetchRead.Shares
  misa : DFrac
  enable : DFrac
  delegation : DFrac
  environment : DFrac
  landing : DFrac
  hart : DFrac

def cycleShares (shares : Shares) : MycpuBare.Shares :=
  ⟨⟨⟨.own 1, shares.privilege, shares.satp⟩, shares.physical⟩,
    shares.misa, shares.enable, shares.delegation, shares.environment,
    shares.landing, .own 1, shares.hart⟩

def controlFootprint (shares : Shares) : RegisterFootprint.Footprint :=
  (MycpuCycleBody.footprint (cycleShares shares)).filter
    (fun cell => cell.1 != .mstatus && !(HartTp.physicalKeys.contains cell.1))

/-- Typed symbolic footprint file. Actual values are backed by pinnedFile;
this pure overlay alone does not assert physical register contents. -/
def entry (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile) : RegisterFile := fun r =>
  match r with
  | .x1 => HartTp.rget cpu values 1#5
  | .x2 => HartTp.rget cpu values 2#5
  | .x3 => HartTp.rget cpu values 3#5
  | .x4 => HartTp.rget cpu values 4#5
  | .x5 => HartTp.rget cpu values 5#5
  | .x6 => HartTp.rget cpu values 6#5
  | .x7 => HartTp.rget cpu values 7#5
  | .x8 => HartTp.rget cpu values 8#5
  | .x9 => HartTp.rget cpu values 9#5
  | .x10 => HartTp.rget cpu values 10#5
  | .x11 => HartTp.rget cpu values 11#5
  | .x12 => HartTp.rget cpu values 12#5
  | .x13 => HartTp.rget cpu values 13#5
  | .x14 => HartTp.rget cpu values 14#5
  | .x15 => HartTp.rget cpu values 15#5
  | .x16 => HartTp.rget cpu values 16#5
  | .x17 => HartTp.rget cpu values 17#5
  | .x18 => HartTp.rget cpu values 18#5
  | .x19 => HartTp.rget cpu values 19#5
  | .x20 => HartTp.rget cpu values 20#5
  | .x21 => HartTp.rget cpu values 21#5
  | .x22 => HartTp.rget cpu values 22#5
  | .x23 => HartTp.rget cpu values 23#5
  | .x24 => HartTp.rget cpu values 24#5
  | .x25 => HartTp.rget cpu values 25#5
  | .x26 => HartTp.rget cpu values 26#5
  | .x27 => HartTp.rget cpu values 27#5
  | .x28 => HartTp.rget cpu values 28#5
  | .x29 => HartTp.rget cpu values 29#5
  | .x30 => HartTp.rget cpu values 30#5
  | .x31 => HartTp.rget cpu values 31#5
  | other => control other

/-- Only these two GPRs have an unrestricted returned value. The remaining
software entries come from restored or framed ownership, not the unowned
GPR projection of MycpuBare's returned symbolic register file. -/
def returnedMap (before : HartTp.GprFile) (after : RegisterFile) : HartTp.GprFile :=
  HartTp.set (HartTp.set before 10#5 (after .x10)) 15#5 (after .x15)

def savedIndices : List HartTp.Index :=
  [2#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5, 26#5, 27#5]

def Saved (before after : HartTp.GprFile) : Prop :=
  ∀ index ∈ savedIndices, after index = before index

/-- Remaining explicit hardware/Bare assumptions. SIE, MPRV/MXR/SXL and
TP are obtained from the owned source component, not additional premises. -/
structure EntryConfig (control : RegisterFile) : Prop where
  privilege : control .cur_privilege = .Supervisor
  active : control .hart_state = .HART_ACTIVE ()
  landing : control .elp = 0#1
  misa : control .misa = 0x800000000014112d#64
  environment : control .menvcfg = 0xa000000000000000#64
  delegated : control .mie &&& ~~~(control .mideleg) = 0#64
  bare : satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 (control .satp))) = some .Bare
  tor : SupervisorPmp.TorRam control
  htif : control .htif_tohost_base = none
  pma : control .pma_regions = pmaBoot
  pc : control .PC = MycpuDecode.address ⟨0, by decide⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def controls (era : Era.Record) (cpu : CPU) (control : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) control (controlFootprint shares)

/-- Exactly 53 physical keys: 21 controls, one mstatus and 31 GPRs.
The pure x0 fact and all bit fragments retain their source meanings. -/
def resources (era : Era.Record) (cpu : CPU) (control : RegisterFile)
    (values : HartTp.GprFile) (shares : Shares) : IProp GF :=
  iprop(controls capacity era cpu control shares ∗
    SupervisorBits.msOwnAt capacity.supervisorBits era cpu (control .mstatus) ∗
    SupervisorBits.offToken capacity.supervisorBits (SupervisorBits.namesOfEra era cpu) ∗
    HartTp.pinnedFile capacity.machine.era.registers era cpu values)

/-- Saved words use the same modular physical source addresses as the
existing function theorem; virtual-tier stack ownership is separate. -/
def stackWords (era : Era.Record) (ξ : TsoContext.CtxId) (control : RegisterFile)
    (cpu : CPU) (values : HartTp.GprFile) (oldRA oldS0 : BitVec 64) : IProp GF :=
  MycpuBare.stackWords capacity.machine era ξ (entry control cpu values) oldRA oldS0

structure Result (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile)
    (after : RegisterFile) : Prop where
  body : MycpuBare.HartResult (entry control cpu values) after cpu
  saved : Saved values (returnedMap values after)
  ra : returnedMap values after 1#5 = values 1#5
  value : returnedMap values after 10#5 = MycpuScalar.mycpuRet (HartTp.hartWord cpu)
  cpuAddress : (returnedMap values after 10#5).toNat = 0x800123e8 + 128 * cpu.val

end Xv6.Kernel.MycpuOff
