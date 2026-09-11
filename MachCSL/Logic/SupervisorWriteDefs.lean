import MachCSL.Logic.TsoContextWriteWPDefs
import MachCSL.Logic.RegisterPlanDefs
import MachCSL.Machine.SupervisorPhysicalDefs

namespace MachCSL.Logic.SupervisorWrite
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

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

/-- Exact present-payload ordinary request, including every metadata field. -/
def request (address : BitVec 64) (word : BitVec 64) : MemoryWriteWP.WriteRequest 8 :=
  { access_kind := .AK_explicit { variety := .AV_plain, strength := .AS_normal }
    va := none, pa := address, translation := (), size := 8, value := some word, tag := none }

abbrev Result := _root_.Sail.Result Bool (physaddr × ExceptionType)

def program (address word : BitVec 64) : SailM Result :=
  checked_mem_write (.Physaddr address) 8 word (.Store .Data)
    .PBMT_PMA .Supervisor () false false false

/-- Actual finite register prefix ending at one real write event. There is no
hypothetical memory transition or resource callback in this judgment. -/
inductive Boundary (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (req : MemoryWriteWP.WriteRequest 8) : SailM α → (MemoryWriteWP.WriteResult → SailM α) → Prop
  | event {k} : Boundary fp rs req (.impure (.writeMem 8 req) k) k
  | prefix {β : Type} {segment : SailM β} {value : β} {next : β → SailM α} {k}
      (before : RegisterPlan.Returns fp rs segment value rs)
      (rest : Boundary fp rs req (next value) k) :
      Boundary fp rs req (segment >>= next) k

/-- Both response branches are retained: any successful optional payload means
true, while the actual write-error response means false, not an exit. -/
def OneWrite (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (address word : BitVec 64) (program : SailM α) (value : Bool → α) : Prop :=
  ∃ tail, Boundary fp rs (request address word) program tail ∧
    (∀ result, tail (.Ok result) = pure (value true)) ∧
    tail (.Err ()) = pure (value false)

end MachCSL.Logic.SupervisorWrite
