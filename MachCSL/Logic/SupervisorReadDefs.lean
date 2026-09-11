import MachCSL.Logic.TsoContextReadWPDefs
import MachCSL.Logic.RegisterPlanDefs
import MachCSL.Machine.SupervisorPhysicalDefs

namespace MachCSL.Logic.SupervisorRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

inductive Kind where | data | pte
  deriving DecidableEq, Repr

def access : Kind → MemoryAccessType mem_payload
  | .data => .Load .Data
  | .pte => .Load .PageTableEntry

structure Shares where
  pma : DFrac
  cfg : DFrac
  addr : DFrac
  htif : DFrac

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.pma_regions, shares.pma), (.pmpcfg_n, shares.cfg),
    (.pmpaddr_n, shares.addr), (.htif_tohost_base, shares.htif)]

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

/-- The actual plain V1 request, identical for these two physical read classes. -/
def request (address : BitVec 64) : MemoryReadWP.ReadRequest 8 :=
  { access_kind := .AK_explicit { variety := .AV_plain, strength := .AS_normal }
    va := none, pa := address, translation := (), size := 8, tag := false }

abbrev Result := _root_.Sail.Result (BitVec 64 × Unit) (physaddr × ExceptionType)

def program (kind : Kind) (address : BitVec 64) : SailM Result :=
  checked_mem_read (access kind) .PBMT_PMA .Supervisor (.Physaddr address) 8
    false false false false

/-- Only the register-only prefix is traversed; the real memory event remains. -/
inductive Boundary (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (req : MemoryReadWP.ReadRequest 8) : SailM α → (MemoryReadWP.ReadResult 8 → SailM α) → Prop
  | event {k} : Boundary fp rs req (.impure (.readMem 8 req) k) k
  | prefix {β : Type} {segment : SailM β} {value : β} {next : β → SailM α} {k}
      (before : RegisterPlan.Returns fp rs segment value rs)
      (rest : Boundary fp rs req (next value) k) :
      Boundary fp rs req (segment >>= next) k

/-- Exact tail behavior for every successful tag and the generated error exit.
This assertion is proved from the program; it is not a read-result assumption. -/
def OneRead (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (address : BitVec 64)
    (program : SailM α) (value : BitVec 64 → α) : Prop :=
  ∃ tail, Boundary fp rs (request address) program tail ∧
    (∀ word tag, tail (.Ok (word, tag)) = pure (value word)) ∧
    tail (.Err ()) = _root_.Sail.ConcurrencyInterfaceV1.Free.fail .Exit

end MachCSL.Logic.SupervisorRead
