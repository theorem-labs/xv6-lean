import Xv6.Kernel.MycpuCycleDefs
import Xv6.Kernel.MycpuRegisterSequenceDefs
import MachCSL.Logic.StackPhysicalDefs

/-! Resource and result contract for the complete Bare mycpu body. This does
not define an executable replacement for the fourteen actual machine cycles. -/
namespace Xv6.Kernel.MycpuBare
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Shares := MycpuCycle.Shares
abbrev cells := @MycpuCycle.cells
abbrev shared := @MycpuCycle.shared

/-- Source-supported initial hardware facts; clock values and pending pins are arbitrary. -/
structure SupervisorConfig (rs : RegisterFile) : Prop where
  privilege : rs .cur_privilege = .Supervisor
  active : rs .hart_state = .HART_ACTIVE ()
  landing : rs .elp = 0#1
  misa : rs .misa = 0x800000000014112d#64
  environment : rs .menvcfg = 0xa000000000000000#64
  sie : (_get_Mstatus_SIE (rs .mstatus) == 1#1) = false
  mprv : _get_Mstatus_MPRV (rs .mstatus) = 0#1
  mxr : _get_Mstatus_MXR (rs .mstatus) = 0#1
  sxl : _get_Mstatus_SXL (rs .mstatus) = 2#2
  delegated : rs .mie &&& ~~~(rs .mideleg) = 0#64
  bare : satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 (rs .satp))) = some .Bare
  tor : SupervisorPmp.TorRam rs
  htif : rs .htif_tohost_base = none
  pma : rs .pma_regions = pmaBoot

structure EntryConfig (rs : RegisterFile) : Prop extends SupervisorConfig rs where
  pc : rs .PC = MycpuDecode.address ⟨0, by decide⟩

/-- SP and S0 are already in the common 28-cell bundle. -/
def remainingSaved : List Register :=
  [.x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

abbrev FrameShares := Register → DFrac

def frameFootprint (shares : FrameShares) : RegisterFootprint.Footprint :=
  remainingSaved.map (fun r => (r, shares r))

def calleeFrame {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : FrameShares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (frameFootprint shares)

/-- Source modular save locations, upper RA slot before the lower S0 slot. -/
def raSlot (entry : RegisterFile) : MachCSL.Memory.PhysicalAddress := StackPhysical.paStk (entry .x2) 1
def s0Slot (entry : RegisterFile) : MachCSL.Memory.PhysicalAddress := StackPhysical.paStk (entry .x2) 2

def stackWords {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (ξ : TsoContext.CtxId) (entry : RegisterFile)
    (raWord s0Word : BitVec 64) : IProp GF :=
  iprop(TsoContextReadWP.wordPointsto capacity era ξ (raSlot entry) (.own 1) raWord ∗
    TsoContextReadWP.wordPointsto capacity era ξ (s0Slot entry) (.own 1) s0Word)

/-- Exact unchanged read-only controls, TP and retirement configuration. -/
def stableRegisters : List Register :=
  [.misa, .mstatus, .cur_privilege, .satp, .pmpcfg_n, .pmpaddr_n, .pma_regions,
   .htif_tohost_base, .mie, .mideleg, .menvcfg, .elp, .x4,
   .mcountinhibit, .minstretcfg, .hart_state]

def Stable (entry after : RegisterFile) : Prop :=
  ∀ r ∈ stableRegisters, after r = entry r

/-- Actual register result at the returned cycle boundary. Stack scratch contents
are returned separately; clocks are intentionally not assigned a fixed value. -/
structure Result (entry after : RegisterFile) : Prop where
  config : SupervisorConfig after
  stable : Stable entry after
  pc : after .PC = MycpuReturn.retPC (entry .x1)
  nextPC : after .nextPC = MycpuReturn.retPC (entry .x1)
  saved : CalleeSaved.Preserved entry after
  ra : after .x1 = entry .x1
  value : after .x10 = MycpuScalar.mycpuRet (entry .x4)

structure HartResult (entry after : RegisterFile) (cpu : CPU) : Prop extends Result entry after where
  cpuAddress : (after .x10).toNat = 0x800123e8 + 128 * cpu.val

end Xv6.Kernel.MycpuBare
