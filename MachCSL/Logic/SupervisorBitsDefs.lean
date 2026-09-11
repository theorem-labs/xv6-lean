import MachCSL.Logic.EraDefs
import Iris.Instances.Lib.GhostVar
import LeanPaperStock.SysRegs

/-! Source `IntrDefs.v:196–207,309–452,649–653,751,932–936`.
This is the bit/mstatus resource component, not full sconf or an enabled
interrupt arm. Slot 44 is reserved; no runtime ownership is allocated here. -/
namespace MachCSL.Logic.SupervisorBits
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

abbrev Bit := BitVec 1
abbrev BitRF := GhostVarF Bit
def bitFunctor : GFunctor := ⟨BitRF, inferInstance⟩
def slot : Nat := 44

structure Capacity (GF : BundledGFunctors) where
  registers : Registers.Capacity GF
  bits : GhostVarG GF Bit

structure Names where
  sie : GName
  spp : GName
  spie : GName

def namesOfEra (era : Era.Record) (cpu : CPU) : Names :=
  ⟨era.supervisorInterruptEnable cpu, era.supervisorPreviousPrivilege cpu,
    era.supervisorPreviousInterruptEnable cpu⟩

def half : Qp := (1 : Qp).half
def quarter : Qp := half.half
def eighth : Qp := quarter.half
def sieBit (enabled : Bool) : Bit := if enabled then 1#1 else 0#1

/-- Exact pure nominal-privilege helper, `WpGprCsrwCommon.v:240–243`. -/
def haveNominalValue (privilege : BitVec 2) : Bool :=
  if privilege == 0#2 then true
  else if privilege == 1#2 then true
  else if privilege == 2#2 then false else true

/-- All ten conjuncts of the source SIE-agnostic mstatus fact set. -/
def MsFacts (ms : BitVec 64) : Prop :=
  (_get_Mstatus_MPRV ms == 1#1) = false ∧
  _get_Mstatus_SXL ms = 2#2 ∧
  (_get_Mstatus_MXR ms == 0#1) = true ∧
  (_get_Mstatus_TSR ms == 1#1) = false ∧
  _get_Mstatus_XS ms = extStatus_map_forwards .Off ∧
  _get_Mstatus_FS ms = extStatus_map_forwards .Off ∧
  _get_Mstatus_VS ms = extStatus_map_forwards .Off ∧
  _get_Mstatus_SD ms = 0#1 ∧
  haveNominalValue (_get_Mstatus_MPP ms) = true ∧
  (_get_Mstatus_TVM ms == 1#1) = false

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def bit (name : GName) (q : Qp) (value : Bit) : IProp GF :=
  letI := capacity.bits
  ghost_var name (.own q) value

def sretBits (names : Names) (spp spie : Bit) : IProp GF :=
  iprop(bit capacity names.spp half spp ∗ bit capacity names.spie half spie)

def sretTie (names : Names) (ms : BitVec 64) : IProp GF :=
  sretBits capacity names (_get_Mstatus_SPP ms) (_get_Mstatus_SPIE ms)

/-- Exact source `sconf_msown`, with runtime names made explicit. -/
def msOwn (registerName : GName) (names : Names) (ms : BitVec 64) : IProp GF :=
  iprop(Registers.regPointsto capacity.registers registerName .mstatus (.own 1) ms ∗
    bit capacity names.sie half (_get_Mstatus_SIE ms) ∗
    sretTie capacity names ms ∗ ⌜MsFacts ms⌝)

/-- Only the arm's ghost eighth; the enabled handler payload is not defined here. -/
def armBit (names : Names) (enabled : Bool) : IProp GF :=
  bit capacity names.sie eighth (sieBit enabled)

def offToken (names : Names) : IProp GF := armBit capacity names false

def countBit (names : Names) (depth : Nat) (baseEnabled : Bool) : IProp GF :=
  bit capacity names.sie eighth (if depth = 0 then sieBit baseEnabled else 0#1)

/-- The remaining fragments from raw allocation. All are retained. A quarter
is not by itself evidence of an installed handler. -/
def allocationRemainder (names : Names) (ms : BitVec 64) : IProp GF :=
  iprop(bit capacity names.sie eighth (_get_Mstatus_SIE ms) ∗
    bit capacity names.sie eighth (_get_Mstatus_SIE ms) ∗
    bit capacity names.sie quarter (_get_Mstatus_SIE ms) ∗ sretTie capacity names ms)

def msOwnAt (era : Era.Record) (cpu : CPU) (ms : BitVec 64) : IProp GF :=
  msOwn capacity (era.registers cpu) (namesOfEra era cpu) ms

end MachCSL.Logic.SupervisorBits
