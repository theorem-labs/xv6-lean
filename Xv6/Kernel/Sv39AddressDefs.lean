import Xv6.Kernel.KptTranslateDefs
import Xv6.Kernel.KptResidueDefs
import MachCSL.Machine.SupervisorBareDefs

/-! The actual supervisor Sv39 outer address program, before shared
translation is supplied. All errors remain Sail results, not success premises. -/
namespace Xv6.Kernel.Sv39Address
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MachineInterp.Capacity
abbrev Shares := SupervisorBare.Shares
abbrev footprint := SupervisorBare.footprint
abbrev Supported := KptLeaf.Supported
abbrev Effective := SupervisorBare.Effective
abbrev Result := _root_.Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)

structure Config (rs : RegisterFile) (root : PtTree.PPN) : Prop where
  privilege : rs .cur_privilege = .Supervisor
  sxl : _get_Mstatus_SXL (rs .mstatus) = 2#2
  rooted : KptResidue.SatpRooted root (rs .satp)

def Canonical (address : BitVec 64) : Prop :=
  address = (address.extractLsb' 0 39).signExtend 64

def vpn (address : BitVec 64) : PtTree.VPN := address.extractLsb' 12 27

def physical (ppn : PtTree.PPN) (address : BitVec 64) : BitVec 64 :=
  (BitVec.append ppn (address.extractLsb' 0 12)).zeroExtend 64

def mxr (rs : RegisterFile) : Bool := _get_Mstatus_MXR (rs .mstatus) == 1#1

def doSum (rs : RegisterFile) : Bool := _get_Mstatus_SUM (rs .mstatus) == 1#1

def program (address : BitVec 64) (access : MemoryAccessType mem_payload) : SailM Result :=
  translateAddr (.Virtaddr address) access

/-- This result classifier is specified only for `Supported` accesses.
The store/AMO cases share the actual SAMO exceptions. -/
def pageFault : MemoryAccessType mem_payload → ExceptionType
  | .InstructionFetch () => .E_Fetch_Page_Fault ()
  | .Load .Data => .E_Load_Page_Fault ()
  | _ => .E_SAMO_Page_Fault ()

def accessFault : MemoryAccessType mem_payload → ExceptionType
  | .InstructionFetch () => .E_Fetch_Access_Fault ()
  | .Load .Data => .E_Load_Access_Fault ()
  | _ => .E_SAMO_Access_Fault ()

/-- No operational use or claim is made for unsupported payloads. -/
def fault (access : MemoryAccessType mem_payload) : PTW_Error → ExceptionType
  | .PTW_Ext_Error ext => .E_Extension (ext_translate_exception ext)
  | .PTW_No_Access () => accessFault access
  | _ => pageFault access

/-- Keep the real error callback. Success concatenates all 44 PPN bits and
12 offset bits before extending to the actual 64-bit physical address. -/
def resume (address : BitVec 64) (access : MemoryAccessType mem_payload) :
    KptTranslate.Result → SailM Result
  | .Ok (ppn, pbmt, ext) => pure (.Ok (.Physaddr (physical ppn address), pbmt, ext))
  | .Err (error, ext) => do
      let exception ← translationException access error
      pure (.Err (exception, ext))

def resumed (address : BitVec 64) (access : MemoryAccessType mem_payload) :
    KptTranslate.Result → Result
  | .Ok (ppn, pbmt, ext) => .Ok (.Physaddr (physical ppn address), pbmt, ext)
  | .Err (error, ext) => .Err (fault access error, ext)

/-- A checked register prefix followed by the exact translation program.
This relation is a pure program decomposition, not a WP/access callback. -/
inductive Boundary (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (body : SailM α) : SailM β → (α → SailM β) → Prop where
  | body (tail : α → SailM β) : Boundary fp rs body (body >>= tail) tail
  | «prefix» {γ : Type} {segment : SailM γ} {value : γ}
      {next : γ → SailM β} {tail : α → SailM β}
      (before : RegisterPlan.Returns fp rs segment value rs)
      (rest : Boundary fp rs body (next value) tail) :
      Boundary fp rs body (segment >>= next) tail

abbrev cells {GF : BundledGFunctors} (capacity : Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

end Xv6.Kernel.Sv39Address
