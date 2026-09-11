import Xv6.Kernel.KptAddressDefs
import Xv6.Kernel.KernelDatumWord4Defs
import Xv6.Kernel.KptMemoryDefs
import MachCSL.Logic.SupervisorAddressDefs
import MachCSL.Logic.SupervisorWriteEA4Defs

/-! Ordinary four-byte virtual data programs. Translation and data events
remain separate; the source virtual/context word is the only datum input. -/
namespace Xv6.Kernel.KptMemory4
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptAddress.Capacity
abbrev Shares := KptAddress.Shares
abbrev Kind := SupervisorAddress.Kind
abbrev access := SupervisorAddress.access
abbrev auxiliaryCells := @KptAddress.auxiliaryCells

/-- The same five actual ambient controls as the eight-byte boundary. -/
abbrev Ambient := KptMemory.Ambient
abbrev transformShares := KptMemory.transformShares

def Result : Kind → Type
  | .load => _root_.Sail.Result (BitVec 32) ExecutionResult
  | .store => _root_.Sail.Result Bool ExecutionResult

def addressProgram [Platform] (kind : Kind) (va : BitVec 64) (new : BitVec 32) : SailM (Result kind) :=
  match kind with
  | .load => vmem_read_addr (.Virtaddr va) 4 (.Load .Data) false false false
  | .store => vmem_write_addr (.Virtaddr va) 4 new (.Store .Data) false false false

/-- The real transform call at the already-computed effective virtual
address. Base-register/extension hooks and full instruction execution are
outside this boundary. -/
def program [Platform] (kind : Kind) (va : BitVec 64) (new : BitVec 32) : SailM (Result kind) :=
  match kind with
  | .load => do
      let transformed ← transform_effective_address (.Virtaddr va) (.Load .Data)
      vmem_read_addr transformed 4 (.Load .Data) false false false
  | .store => do
      let transformed ← transform_effective_address (.Virtaddr va) (.Store .Data)
      vmem_write_addr transformed 4 new (.Store .Data) false false false

def valueAfter : Kind → BitVec 32 → BitVec 32 → BitVec 32
  | .load, old, _ => old
  | .store, _, new => new

def result (kind : Kind) (old : BitVec 32) : Result kind :=
  match kind with
  | .load => .Ok old
  | .store => .Ok true

/-- Raw residuals retain the actual exception callbacks and offset address. -/
def readAfterMemory (va : BitVec 64) (pa : physaddr) : SupervisorMemOuter4.ReadResult → SailM (Result .load)
  | .Ok word => pure (.Ok word)
  | .Err (excPa, error) => do
      let failure ← memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error
      pure (.Err failure)

def readAfterAddress (va : BitVec 64) : KptAddress.Result → SailM (Result .load)
  | .Err (error, _) => do
      let failure ← memory_exception (.Virtaddr va) error
      pure (.Err failure)
  | .Ok (pa, pbmt, _) =>
      mem_read (.Load .Data) pbmt pa 4 false false false >>= readAfterMemory va pa

def writeAfterMemory (va : BitVec 64) (pa : physaddr) : SupervisorWrite4.Result → SailM (Result .store)
  | .Ok success => pure (.Ok success)
  | .Err (excPa, error) => do
      let failure ← memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error
      pure (.Err failure)

def writeAfterEA [Platform] (va : BitVec 64) (new : BitVec 32) (pa : physaddr) (pbmt : page_based_mem_type) :
    SupervisorWriteEA4.Result → SailM (Result .store)
  | .Err (excPa, error) => do
      let failure ← memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error
      pure (.Err failure)
  | .Ok () => mem_write_value pa 4 new (.Store .Data) pbmt false false false >>= writeAfterMemory va pa

def writeAfterAddress [Platform] (va : BitVec 64) (new : BitVec 32) : KptAddress.Result → SailM (Result .store)
  | .Err (error, _) => do
      let failure ← memory_exception (.Virtaddr va) error
      pure (.Err failure)
  | .Ok (pa, pbmt, _) =>
      mem_write_ea pa 4 (.Store .Data) pbmt false false false >>= writeAfterEA va new pa pbmt

def afterAddress [Platform] (kind : Kind) (va : BitVec 64) (new : BitVec 32) : KptAddress.Result → SailM (Result kind) :=
  match kind with
  | .load => readAfterAddress va
  | .store => writeAfterAddress va new

def afterReservation (kind : Kind) (va : BitVec 64) (rr : Option Reservation)
    (outcome : KptAddress.Outcome) : Option Reservation :=
  match kind with
  | .load => KptAddress.afterReservation va rr outcome
  | .store => none

/-- Both assertions are proved after native translation. They never occur
as a caller precondition or successful-response assumption. -/
def CompletedFacts (rs : RegisterFile) (data : KptAddress.Data) (root : PtTree.PPN)
    (kind : Kind) (va : BitVec 64) (ppn : PtTree.PPN) (outcome : KptAddress.Outcome) : Prop :=
  KptAddress.OutcomeFacts rs data root va ppn .rw (access kind) outcome ∧
    KptAddress.result va ppn (access kind) outcome =
      .Ok (.Physaddr (KernelDatum.physical ppn va), .PBMT_PMA, ())

variable {GF : BundledGFunctors} (capacity : Capacity GF) {hlc : HasLC} [InvGS_gen hlc GF]

/-- Return the folded source residue, with its actual coherent post-TLB;
keep all translation receipts and add the data event's own view receipt. -/
noncomputable def resources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (kind : Kind) (tier : KernelDatum.Tier)
    (ξ : TsoContext.CtxId) (va : BitVec 64) (dq : DFrac) (old new : BitVec 32)
    (rr : Option Reservation) (outcome : KptAddress.Outcome) (view : Nat) : IProp GF :=
  iprop(auxiliaryCells capacity era cpu rs shares ∗ KptResidue.residue capacity era cpu N root ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    KernelDatumWord4.word capacity era tier ξ va dq (valueAfter kind old new) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (afterReservation kind va rr outcome) ∗ KptAddress.receipts capacity era cpu va outcome ∗
    Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view)

noncomputable def continueWith [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (kind : Kind) (tier : KernelDatum.Tier)
    (ξ : TsoContext.CtxId) (va : BitVec 64) (dq : DFrac) (old new : BitVec 32)
    (rr : Option Reservation) (continuation : Result kind → SailM Unit) (post : Empty → IProp GF)
    (ppn : PtTree.PPN) (data : KptAddress.Data) (outcome : KptAddress.Outcome) : IProp GF :=
  iprop(⌜CompletedFacts rs data root kind va ppn outcome⌝ -∗ ▷ (∀ view,
    resources capacity era cpu rs shares N root kind tier ξ va dq old new rr outcome view -∗
    MemoryReadWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (continuation (result kind old))) post))

/-- Translation guards keep their original order and dynamic result scope;
the innermost additional guard pays exactly one ordinary data event. -/
noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (kind : Kind) (tier : KernelDatum.Tier)
    (ξ : TsoContext.CtxId) (va : BitVec 64) (dq : DFrac) (old new : BitVec 32)
    (rr : Option Reservation) (continuation : Result kind → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  let next := continueWith capacity image fixed whole gen era cpu rs shares N root kind tier ξ va dq old new rr continuation post
  iprop(∀ ppn data tree p2 p1 referenceA referenceD,
    (∀ a d update, KptAD.guarded update
      (next ppn data (.translated tree p2 p1 referenceA referenceD (.hit a d update)))) ∧
    ▷ ▷ ▷ (∀ a d view2 view1 view0 update, KptAD.guarded update
      (next ppn data (.translated tree p2 p1 referenceA referenceD (.miss a d view2 view1 view0 update)))))

end Xv6.Kernel.KptMemory4
