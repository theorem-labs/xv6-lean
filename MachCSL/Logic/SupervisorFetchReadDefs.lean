import MachCSL.Logic.TsoContextBytesReadWPDefs
import MachCSL.Logic.RegisterPlanDefs
import MachCSL.Machine.SupervisorPhysicalDefs

namespace MachCSL.Logic.SupervisorFetchRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

def Supported (n : Nat) : Prop := n = 2 ∨ n = 4

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

/-- The actual plain V1 request, including the instruction-fetch path’s actual plain kind. -/
def request (address : BitVec 64) (n : Nat) : MemoryReadWP.ReadRequest n :=
  { access_kind := .AK_explicit { variety := .AV_plain, strength := .AS_normal }
    va := none, pa := address, translation := (), size := n, tag := false }

abbrev Result (n : Nat) := _root_.Sail.Result (BitVec (8 * n) × Unit) (physaddr × ExceptionType)

def program (address : BitVec 64) (n : Nat) : SailM (Result n) :=
  checked_mem_read (.InstructionFetch ()) .PBMT_PMA .Supervisor (.Physaddr address) n
    false false false false

/-- Only the register-only prefix is traversed; the real memory event remains. -/
inductive Boundary (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    {n : Nat} (req : MemoryReadWP.ReadRequest n) : SailM α → (MemoryReadWP.ReadResult n → SailM α) → Prop
  | event {k} : Boundary fp rs req (.impure (.readMem n req) k) k
  | prefix {β : Type} {segment : SailM β} {value : β} {next : β → SailM α} {k}
      (before : RegisterPlan.Returns fp rs segment value rs)
      (rest : Boundary fp rs req (next value) k) :
      Boundary fp rs req (segment >>= next) k

/-- Exact tail behavior for every successful tag and the generated error exit.
This assertion is proved from the program; it is not a read-result assumption. -/
def OneRead (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (address : BitVec 64)
    (n : Nat) (program : SailM α) (value : BitVec (8 * n) → α) : Prop :=
  ∃ tail, Boundary fp rs (request address n) program tail ∧
    (∀ word tag, tail (.Ok (word, tag)) = pure (value word)) ∧
    tail (.Err ()) = _root_.Sail.ConcurrencyInterfaceV1.Free.fail .Exit

end MachCSL.Logic.SupervisorFetchRead
