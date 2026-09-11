import MachCSL.Machine.SpinlockImageDefs
import MachCSL.Machine.JalLoopUniversalFetch
import MachCSL.Logic.EventPlanDefs

/-! Concrete four-byte data-access boundaries for the integration image.
The register condition does not constrain PC, nextPC, operands or PMP addresses. -/
namespace MachCSL.Machine.SpinlockAccess
open LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1

inductive Location where
  | lock | counter
  deriving DecidableEq, Repr

inductive Mode where
  | load | store | amo
  deriving DecidableEq, Repr

def address : Location → Memory.PhysicalAddress
  | .lock => SpinlockImage.lockAddress
  | .counter => SpinlockImage.counterAddress

def offset : Location → BitVec 64
  | .lock => 0#64
  | .counter => 4#64

def access : Mode → MemoryAccessType mem_payload
  | .load => .Load .Data
  | .store => .Store .Data
  | .amo => .Atomic (.AMOSWAP, true, false, .Data, .Data)

def Mode.exclusive : Mode → Bool
  | .amo => true
  | _ => false

def accessInfo : Phys_Mem_Access_Info := ⟨.CannotSplit, 0⟩

def readKind (exclusive : Bool) : read_kind :=
  if exclusive then .Read_RISCV_reserved_acquire else .Read_plain

def writeKind (exclusive : Bool) : write_kind :=
  if exclusive then .Write_RISCV_conditional else .Write_plain

/-- Actual request emitted by plain loads or the acquire half of AMOSWAP.aq. -/
def readRequest (location : Location) (exclusive : Bool) : Logic.MemoryReadWP.ReadRequest 4 :=
  { access_kind := .AK_explicit
      { variety := if exclusive then .AV_exclusive else .AV_plain
        strength := if exclusive then .AS_rel_or_acq else .AS_normal }
    va := none
    pa := address location
    translation := ()
    size := 4
    tag := false }

/-- AMOSWAP.aq writes exclusively with normal strength; its acquire annotation
belongs to the preceding read. All remaining V1 request fields are explicit. -/
def writeRequest (location : Location) (exclusive : Bool) (word : BitVec 32) :
    Logic.MemoryWriteWP.WriteRequest 4 :=
  { access_kind := .AK_explicit
      { variety := if exclusive then .AV_exclusive else .AV_plain
        strength := .AS_normal }
    va := none
    pa := address location
    translation := ()
    size := 4
    value := some word
    tag := none }

structure Static (rs : RegisterFile) : Prop where
  misa : rs .misa = 0x800000000014112d#64
  mstatus : rs .mstatus = 0xA00000000#64
  menvcfg : rs .menvcfg = 0#64
  mseccfg : rs .mseccfg = 0#64
  privilege : rs .cur_privilege = .Machine
  pma : rs .pma_regions = pmaBoot
  htif : rs .htif_tohost_base = none

end MachCSL.Machine.SpinlockAccess
