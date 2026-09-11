import MachCSL.Logic.MemoryExclusiveWPDefs
import MachCSL.Logic.TsoStoreDefs

/-! Present-payload RAM writes from HartEvents.v:797,841. Complete requests
remain explicit, including the kind, translation, declared size and optional tag. -/
namespace MachCSL.Logic.MemoryWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
open _root_.Sail.ConcurrencyInterfaceV1

abbrev WriteRequest (n : Nat) := Mem_write_request n Arch.va_size Arch.pa Arch.translation Arch.arch_ak
abbrev WriteResult := _root_.Sail.Result (Option Bool) Arch.abort
abbrev threadWP := @DeadThread.threadWP
abbrev writeBundle := @MemoryExclusiveWP.readBundle

@[reducible] def storeCapacity {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF) :
    TsoStore.Capacity GF := ⟨capacity.era.heap, capacity.era.views, capacity.era.history⟩
@[reducible] def storeNames (era : Era.Record) : TsoStore.Names := ⟨era.tsoNames, era.metadata⟩

def postView (g : State) (cpu : CPU) (req : WriteRequest n) : Nat :=
  if accessExclusive req.access_kind then g.log.length + 1 else g.views cpu

def writeState (g : State) (cpu : CPU) (req : WriteRequest n) (value : BitVec (8 * n)) : State :=
  { g with memory := writeBytes g.memory req.pa n value
           log := g.log ++ [⟨snapshot req.pa n value, hartAgent cpu⟩]
           views := updateHart g.views cpu (postView g cpu req)
           reservations := updateHart g.reservations cpu none }

/-- The caller pays the exact physical/TSO change, under the single-step mask
and later. Reservation, fixed-world and observation updates belong to the rule.
The pure premise is supplied by a proved native validity bridge. -/
def checkedPremise {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (P : State → Prop) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ g : State, ⌜P g⌝ -∗ writeBundle capacity.era era g -∗
    Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g ={⊤,∅}=∗
    ▷ (|={∅,⊤}=> writeBundle capacity.era era (writeState g cpu req value) ∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (writeState g cpu req value) ∗
      (Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) (postView g cpu req) -∗
        threadWP capacity image fixed whole (.hart gen cpu (k (.Ok none))) post)))

def writePremise {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (post : Empty → IProp GF) : IProp GF :=
  checkedPremise capacity image fixed whole gen era cpu n req value k (fun _ => True) post

def conditionalPremise {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (old value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (post : Empty → IProp GF) : IProp GF :=
  checkedPremise capacity image fixed whole gen era cpu n req value k
    (fun g => readBytes g.memory req.pa n = some old) post

/-- Resource extraction for the proved TsoStore adapter. The callback returns
the ORIGINAL bundle/TSO and actual full old ledger window, then receives every
new cell and the exact authored receipt to restore its invariant. -/
def ledgerPremise {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (P : State → Prop) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ g : State, ⌜P g⌝ -∗ writeBundle capacity.era era g -∗
    Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g ={⊤,∅}=∗
    ▷ (∃ old : BitVec (8 * n), writeBundle capacity.era era g ∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g ∗
      TsoStore.ledgerWindow (storeCapacity capacity) (storeNames era) req.pa n old ∗
      (TsoStore.storedWindow (storeCapacity capacity) (storeNames era) req.pa n value (g.log.length + 1) -∗
        Tso.History.logElem capacity.era.history era.logEntries g.log.length
          ⟨snapshot req.pa n value, hartAgent cpu⟩ ={∅,⊤}=∗
        (Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
          Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) (postView g cpu req) -∗
          threadWP capacity image fixed whole (.hart gen cpu (k (.Ok none))) post))))

end MachCSL.Logic.MemoryWriteWP
