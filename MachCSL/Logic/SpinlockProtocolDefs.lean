import Iris.Instances.Lib.Invariants
import MachCSL.Logic.EventPlanDefs
import MachCSL.Logic.LockDefs
import MachCSL.Machine.SpinlockAccessDefs

/-! Proposed concrete resource protocol for the integration image. This is a
machine-mode ledger invariant, not the source context-indexed xv6 lock API. -/
namespace MachCSL.Logic.SpinlockProtocol
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure Capacity (GF : BundledGFunctors) where
  machine : MachineInterp.Capacity GF
  lock : Lock.Capacity GF

inductive Phase where
  | idle
  | reserved (old : BitVec 32)
  | held (acquisition : Nat) (counter : BitVec 32) (timestamp : Nat)
  | loaded (acquisition : Nat) (counter : BitVec 32) (timestamp : Nat)
  | stored (acquisition : Nat) (counter : BitVec 32) (timestamp : Nat)
  deriving DecidableEq, Repr

abbrev lockRead := SpinlockAccess.readRequest .lock true
abbrev counterRead := SpinlockAccess.readRequest .counter false
abbrev swapWrite := SpinlockAccess.writeRequest .lock true 1#32
abbrev counterWrite (word : BitVec 32) := SpinlockAccess.writeRequest .counter false word
abbrev unlockWrite := SpinlockAccess.writeRequest .lock false 0#32

inductive PlainStep : Phase → (n : Nat) → EventPlan.ReadRequest n → BitVec (8 * n) → Phase → Prop where
  | load (B v t) : PlainStep (.held B v t) 4 counterRead v (.loaded B v t)

inductive ExclusiveStep : Phase → (n : Nat) → EventPlan.ReadRequest n → BitVec (8 * n) → Phase → Prop where
  | reserve (old : BitVec 32) (binary : old = 0#32 ∨ old = 1#32) :
      ExclusiveStep .idle 4 lockRead old (.reserved old)

inductive WriteStep : Phase → (n : Nat) → EventPlan.WriteRequest n → BitVec (8 * n) → Phase → Prop where
  | acquire (B v t) (visible : t ≤ B) : WriteStep (.reserved 0#32) 4 swapWrite 1#32 (.held B v t)
  | failed : WriteStep (.reserved 1#32) 4 swapWrite 1#32 .idle
  | increment (B v t nextTime) :
      WriteStep (.loaded B v t) 4 (counterWrite (v + 1#32)) (v + 1#32) (.stored B (v + 1#32) nextTime)
  | release (B v t) : WriteStep (.stored B v t) 4 unlockWrite 0#32 .idle

inductive BarrierStep : Phase → barrier_kind → Phase → Prop where
  | fence (B v t) : BarrierStep (.stored B v t) .Barrier_RISCV_rw_w (.stored B v t)

/-- Eligibility selects the proved rule, without adding a hardware guard.
An AMO's old value is justified only by its actual matching reservation. -/
inductive ModeEnabled : Phase → (rr : Option Reservation) → (n : Nat) →
    (req : EventPlan.WriteRequest n) → BitVec (8 * n) → EventPlan.WriteMode n req rr → Prop where
  | swap (old : BitVec 32) (bound : 4 < 2 ^ 64) :
      ModeEnabled (.reserved old) (some (snapshot SpinlockImage.lockAddress 4 old))
        4 swapWrite 1#32 (.reserved old rfl bound)
  | increment (B v t rr) :
      ModeEnabled (.loaded B v t) rr 4 (counterWrite (v + 1#32)) (v + 1#32) .ordinary
  | release (B v t rr) : ModeEnabled (.stored B v t) rr 4 unlockWrite 0#32 .ordinary

def relations : EventPlan.Relations Phase where
  plainEnabled := fun s n req => ∃ word next, PlainStep s n req word next
  exclusiveEnabled := fun s n req => s = .idle ∧
    (⟨n, req⟩ : (n : Nat) × EventPlan.ReadRequest n) = ⟨4, lockRead⟩
  writeEnabled := fun s n req value => ∃ rr mode, ModeEnabled s rr n req value mode
  barrierEnabled := fun s kind => ∃ next, BarrierStep s kind next
  writeModeEnabled := ModeEnabled
  plain := PlainStep
  exclusive := ExclusiveStep
  write := WriteStep
  barrier := BarrierStep

variable {GF : BundledGFunctors} (capacity : Capacity GF)

@[reducible] def storeCapacity : TsoStore.Capacity GF := MemoryWriteWP.storeCapacity capacity.machine
@[reducible] def storeNames (era : Era.Record) : TsoStore.Names := MemoryWriteWP.storeNames era

def wordAt (era : Era.Record) (a : PhysicalAddress) (v : BitVec 32) (t : Nat) : IProp GF :=
  TsoStore.storedWindow (storeCapacity capacity) (storeNames era) a 4 v t

/-- The latest lock timestamp/author is deliberately distinct from its owner
and winning position, because a failed spinner also writes one. -/
def body (era : Era.Record) (γ : GName) : IProp GF :=
  iprop(∃ B lockTime : Nat,
    (wordAt capacity era SpinlockImage.lockAddress 0#32 lockTime ∗
      Lock.authAt capacity.lock γ none B ∗ Lock.fragAt capacity.lock γ none B ∗
      ∃ v : BitVec 32, ∃ t : Nat, wordAt capacity era SpinlockImage.counterAddress v t) ∨
    (∃ owner : CPU, wordAt capacity era SpinlockImage.lockAddress 1#32 lockTime ∗
      Lock.authAt capacity.lock γ (some (owner, false)) B))

/-- Actual winning-append receipt and acquisition view, in addition to the
source camera's matching state/position fragment. No CPU-field write is claimed. -/
def won (era : Era.Record) (γ : GName) (cpu : CPU) (B : Nat) : IProp GF :=
  iprop(Lock.fragAt capacity.lock γ (some (cpu, false)) B ∗
    Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) B ∗
    ⌜0 < B⌝ ∗ Tso.History.logElem capacity.machine.era.history era.logEntries (B - 1)
      ⟨snapshot SpinlockImage.lockAddress 4 1#32, hartAgent cpu⟩)

def payload (era : Era.Record) (γ : GName) (cpu : CPU) : Phase → IProp GF
  | .idle => iprop(True)
  | .reserved old => iprop(⌜old = 0#32 ∨ old = 1#32⌝)
  | .held B v t | .loaded B v t =>
      iprop(won capacity era γ cpu B ∗ wordAt capacity era SpinlockImage.counterAddress v t ∗ ⌜t ≤ B⌝)
  | .stored B v t =>
      iprop(won capacity era γ cpu B ∗ wordAt capacity era SpinlockImage.counterAddress v t)

variable [Platform] {hlc : HasLC} [InvGS_gen hlc GF]

def isLock (N : Namespace) (era : Era.Record) (γ : GName) : IProp GF :=
  inv N (body capacity era γ)

/-- Only persistent scenery is shared; the counter and holder resources stay
linear and the actual reservation remains a separate EventPlan argument. -/
def resource (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (N : Namespace) (γ : GName) (cpu : CPU) (phase : Phase) : IProp GF :=
  iprop(MachineInterp.generationCertificate capacity.machine fixed gen era ∗
    isLock capacity N era γ ∗ payload capacity era γ cpu phase)

end MachCSL.Logic.SpinlockProtocol
