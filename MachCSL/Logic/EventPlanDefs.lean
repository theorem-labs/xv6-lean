import MachCSL.Logic.EventWPDefs
import MachCSL.Logic.MemoryWriteWPDefs
import MachCSL.Logic.BarrierWPDefs

/-! Pure, well-founded plans for interruptible memory/barrier boundaries.
Existing ExecPlan is embedded unchanged. Resource callbacks below contain no WP. -/
namespace MachCSL.Logic.EventPlan
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
abbrev ReadRequest := MemoryReadWP.ReadRequest
abbrev WriteRequest := MemoryWriteWP.WriteRequest

/-- Ordinary writes are unbounded. Reserved writes carry the exact source
snapshot and only its strict byte-extraction bound, without a kind premise. -/
inductive WriteMode (n : Nat) (req : WriteRequest n) (rr : Option Reservation) where
  | ordinary
  | reserved (old : BitVec (8 * n)) (snapshot : rr = some (Memory.snapshot req.pa n old))
      (bound : n < 2 ^ 64)

/-- Pure branch labels; their truth must be established by the actual
resource callback, never assumed to restrict the machine's result choices. -/
structure Relations (S : Type) where
  plainEnabled : S → (n : Nat) → ReadRequest n → Prop
  exclusiveEnabled : S → (n : Nat) → ReadRequest n → Prop
  writeEnabled : S → (n : Nat) → WriteRequest n → BitVec (8 * n) → Prop
  barrierEnabled : S → barrier_kind → Prop
  /-- Eligibility of the proof rule, not an additional hardware guard. -/
  writeModeEnabled : S → (rr : Option Reservation) → (n : Nat) →
    (req : WriteRequest n) → BitVec (8 * n) → WriteMode n req rr → Prop
  plain : S → (n : Nat) → ReadRequest n → BitVec (8 * n) → S → Prop
  exclusive : S → (n : Nat) → ReadRequest n → BitVec (8 * n) → S → Prop
  write : S → (n : Nat) → WriteRequest n → BitVec (8 * n) → S → Prop
  barrier : S → barrier_kind → S → Prop

def PlainAllowed (rel : Relations S) (s : S) (n : Nat) (req : ReadRequest n)
    (word : BitVec (8 * n)) : Prop := ∃ next, rel.plain s n req word next

def WriteFact (mode : WriteMode n req rr) (g : State) : Prop :=
  match mode with
  | .ordinary => True
  | .reserved old _ _ => readBytes g.memory req.pa n = some old

/-- Each boundary is one real free-tree event. An AMO must have separate
read and write constructors, including its intervening actual prefix plans. -/
inductive Plan (reads : EventWP.ReadAllowed) (rel : Relations S) :
    RegisterFile → Option Reservation → S → SailM α →
      (α → RegisterFile → Option Reservation → S → Prop) → Prop where
  | pure {rs rr s value Q} (good : Q value rs rr s) : Plan reads rel rs rr s (.pure value) Q
  | prefix {rs rr s program next P Q}
      (first : EventWP.ExecPlan reads rs program P)
      (rest : ∀ value after, P value after → Plan reads rel after rr s (next value) Q) :
      Plan reads rel rs rr s (program >>= next) Q
  | plain {rs rr s n req k Q}
      (enabled : rel.plainEnabled s n req)
      (ram : deviceAddress req.pa = false) (kind : accessExclusive req.access_kind = false)
      (rest : ∀ word next, rel.plain s n req word next →
        Plan reads rel rs rr next (k (.Ok (word, none))) Q) :
      Plan reads rel rs rr s (.impure (.readMem n req) k) Q
  | exclusive {rs rr s n req k Q}
      (enabled : rel.exclusiveEnabled s n req)
      (ram : deviceAddress req.pa = false) (kind : accessExclusive req.access_kind = true)
      (rest : ∀ word next, rel.exclusive s n req word next →
        Plan reads rel rs (some (snapshot req.pa n word)) next (k (.Ok (word, none))) Q) :
      Plan reads rel rs rr s (.impure (.readMem n req) k) Q
  | write {rs rr s n req value k Q}
      (enabled : rel.writeEnabled s n req value)
      (present : req.value = some value) (ram : deviceAddress req.pa = false)
      (mode : WriteMode n req rr)
      (eligible : rel.writeModeEnabled s rr n req value mode)
      (rest : ∀ next, rel.write s n req value next → Plan reads rel rs none next (k (.Ok none)) Q) :
      Plan reads rel rs rr s (.impure (.writeMem n req) k) Q
  | barrier {rs rr s kind k Q}
      (enabled : rel.barrierEnabled s kind)
      (rest : ∀ next, rel.barrier s kind next → Plan reads rel rs rr next (k ()) Q) :
      Plan reads rel rs rr s (.impure (.barrier kind) k) Q

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]

/-- Mutable plain reads cover EVERY allowed view and EVERY returned word.
The original power interpretation is restored before the leaf advances its
view; the actual resulting view receipt then selects the next client resource. -/
def PlainAccess (capacity : MachineInterp.Capacity GF)
    (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (rel : Relations S) (R : S → IProp GF) : Prop :=
  ∀ s n (req : ReadRequest n), rel.plainEnabled s n req →
    iprop(⊢ R s -∗ ∀ g : State, ⌜ThreadLive g gen⌝ -∗
      MachineInterp.powerInterp capacity fixed g ={⊤,∅}=∗
      ⌜∀ view, g.views cpu ≤ view → view ≤ g.log.length →
        ∃ word, ReadsBytes g.image g.log (hartAgent cpu) view req.pa n word ∧
          PlainAllowed rel s n req word⌝ ∗
      ▷ (|={∅,⊤}=> MachineInterp.powerInterp capacity fixed g ∗
        ∀ view word, ⌜g.views cpu ≤ view⌝ -∗ ⌜view ≤ g.log.length⌝ -∗
          ⌜ReadsBytes g.image g.log (hartAgent cpu) view req.pa n word⌝ -∗
          ⌜PlainAllowed rel s n req word⌝ -∗
          Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
          ∃ next, ⌜rel.plain s n req word next⌝ ∗ R next))

/-- Exclusive success uses the actual current bytes and advanced TSO resource.
Its callback closes before the separately proved next memory event. -/
def ExclusiveAccess (capacity : MachineInterp.Capacity GF) (era : Era.Record) (cpu : CPU)
    (rel : Relations S) (R : S → IProp GF) : Prop :=
  ∀ s n (req : ReadRequest n), rel.exclusiveEnabled s n req →
    iprop(⊢ R s -∗ ∀ g : State, MemoryExclusiveWP.readBundle capacity.era era g -∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes
        (TsoRead.advanceView g cpu g.log.length) -∗
      Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) g.log.length ={⊤,∅}=∗
      ∃ word : BitVec (8 * n), ⌜readBytes g.memory req.pa n = some word⌝ ∗
        ▷ (|={∅,⊤}=> MemoryExclusiveWP.readBundle capacity.era era g ∗
          Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes
            (TsoRead.advanceView g cpu g.log.length) ∗
          ∃ next, ⌜rel.exclusive s n req word next⌝ ∗ R next))

/-- Exact physical update interface, without a WP oracle. Concrete word
implementations discharge it using TsoStore ledger extraction/restoration. -/
def WriteAccess (capacity : MachineInterp.Capacity GF) (era : Era.Record) (cpu : CPU)
    (rel : Relations S) (R : S → IProp GF) : Prop :=
  ∀ s rr n (req : WriteRequest n) value (mode : WriteMode n req rr), rel.writeEnabled s n req value →
    rel.writeModeEnabled s rr n req value mode →
    iprop(⊢ R s -∗ ∀ g : State, ⌜WriteFact mode g⌝ -∗
      MemoryWriteWP.writeBundle capacity.era era g -∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g ={⊤,∅}=∗
      ▷ (|={∅,⊤}=> MemoryWriteWP.writeBundle capacity.era era (MemoryWriteWP.writeState g cpu req value) ∗
        Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (MemoryWriteWP.writeState g cpu req value) ∗
        (Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu)
            (MemoryWriteWP.postView g cpu req) -∗
          ∃ next, ⌜rel.write s n req value next⌝ ∗ R next)))

def BarrierAccess (capacity : MachineInterp.Capacity GF) (era : Era.Record)
    (rel : Relations S) (R : S → IProp GF) : Prop :=
  ∀ s kind, rel.barrierEnabled s kind → iprop(⊢ BarrierWP.ghostStep capacity.era era (R s)
    (iprop(∃ next, ⌜rel.barrier s kind next⌝ ∗ R next)))

/-- All callbacks are resource transformations. Register/code ownership and
reservation fragments are carried separately by the fold, not duplicated here. -/
structure Access (capacity : MachineInterp.Capacity GF)
    (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (rel : Relations S) (R : S → IProp GF) : Prop where
  plain : PlainAccess capacity fixed gen era cpu rel R
  exclusive : ExclusiveAccess capacity era cpu rel R
  write : WriteAccess capacity era cpu rel R
  barrier : BarrierAccess capacity era rel R

end MachCSL.Logic.EventPlan
