import MachCSL.Logic.EventPlanSpec
import MachCSL.Logic.EventWPProofs

/-! Existing ExecPlan generalized to an actual monadic continuation. -/
namespace MachCSL.Logic.EventPlan
open Iris Iris.Std Iris.BI MachCSL.Machine

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]

omit [Platform] in
theorem pure_bind_eq {A B : Type} (value : A) (k : A → SailM B) :
    ((Sail.ArchSem.FreeM.pure value : SailM A) >>= k) = k value := rfl

omit [Platform] in
theorem impure_bind_eq {A B : Type} (event : Sail.ConcurrencyInterfaceV1.Free.Event RegisterType exception)
    (next : event.Result → SailM A) (k : A → SailM B) :
    ((Sail.ArchSem.FreeM.impure event next : SailM A) >>= k) =
      .impure event (fun value => next value >>= k) := rfl

omit [Platform] in
theorem read_bind_eq {A B : Type} (r : Register) (next : RegisterType r → SailM A)
    (k : A → SailM B) :
    ((Sail.ArchSem.FreeM.impure (.readReg r) next : SailM A) >>= k) =
      .impure (.readReg r) (fun (value : RegisterType r) => (next value >>= k : SailM B)) := rfl

omit [Platform] in
theorem write_bind_eq {A B : Type} (r : Register) (value : RegisterType r)
    (next : Unit → SailM A) (k : A → SailM B) :
    ((Sail.ArchSem.FreeM.impure (.writeReg r value) next : SailM A) >>= k) =
      .impure (.writeReg r value) (fun (result : Unit) => (next result >>= k : SailM B)) := rfl

omit [Platform] in
theorem readMem_bind_eq {A B : Type} (n : Nat) (req : ReadRequest n)
    (next : MemoryReadWP.ReadResult n → SailM A) (k : A → SailM B) :
    ((Sail.ArchSem.FreeM.impure (.readMem n req) next : SailM A) >>= k) =
      .impure (.readMem n req) (fun (value : MemoryReadWP.ReadResult n) =>
        (next value >>= k : SailM B)) := rfl

omit [Platform] in
theorem writeMem_bind_eq {A B : Type} (n : Nat) (req : WriteRequest n)
    (next : MemoryWriteWP.WriteResult → SailM A) (k : A → SailM B) :
    ((Sail.ArchSem.FreeM.impure (.writeMem n req) next : SailM A) >>= k) =
      .impure (.writeMem n req) (fun (value : MemoryWriteWP.WriteResult) =>
        (next value >>= k : SailM B)) := rfl

/-- The prefix may return any Lean value; its machine expression continues
with the actual `continuation`, rather than treating that value as a machine value. -/
theorem fold_bind (facts : EventWP.InitialMapFacts) (capacity : MachineInterp.Capacity GF)
    (registerRules : RegisterWP.RegisterWPSpec capacity) (memoryRules : MemoryReadWP.MemoryReadWPSpec capacity)
    {A : Type} (reads : EventWP.ReadAllowed) (dq : DFrac) (code : IProp GF) (era : Era.Record)
    (access : EventWP.RamAccess capacity era reads dq code)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (cpu : CPU) (rs : RegisterFile) (program : SailM A)
    (Q : A → RegisterFile → Prop) (continuation : A → SailM Unit) (post : Empty → IProp GF)
    (plan : EventWP.ExecPlan reads rs program Q) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗ code -∗
      (∀ value after, ⌜Q value after⌝ -∗
        EventWP.ownedCells capacity.era.registers (era.registers cpu) after -∗ code -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation value)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction plan with
  | @pure rs value Q good =>
    rw [pure_bind_eq]
    iintro #Hcert Hregs Hcode Hfinish
    iapply Hfinish $$ %value %rs [] Hregs Hcode
    ipureintro
    exact good
  | @readOwned rs r k Q owned rest ih =>
    rw [read_bind_eq]
    iintro #Hcert Hregs Hcode Hfinish
    ihave ⟨Hcell, Hrestore⟩ := EventWP.ownedCells_access facts capacity.era.registers
      (era.registers cpu) rs r owned $$ Hregs
    iapply registerRules.read image fixed whole gen era cpu r (.own 1) (rs r)
      (fun value => k value >>= continuation) post $$ Hcert Hcell
    iintro !> Hcell
    ihave Hregs := Hrestore $$ %(rs r) Hcell
    rw [Sail.Registers.write_current]
    iapply ih $$ Hcert Hregs Hcode Hfinish
  | @readPin rs r k Q pin rest ih =>
    rw [read_bind_eq]
    iintro #Hcert Hregs Hcode Hfinish
    iapply registerRules.readAny image fixed whole gen era cpu r
      (fun value => k value >>= continuation) post $$ Hcert
    iintro !> %value
    iapply ih value $$ Hcert Hregs Hcode Hfinish
  | @writeOwned rs r value k Q owned rest ih =>
    rw [write_bind_eq]
    iintro #Hcert Hregs Hcode Hfinish
    ihave ⟨Hcell, Hrestore⟩ := EventWP.ownedCells_access facts capacity.era.registers
      (era.registers cpu) rs r owned $$ Hregs
    iapply registerRules.write image fixed whole gen era cpu r (rs r) value
      (fun result => k result >>= continuation) post $$ Hcert Hcell
    iintro !> Hcell
    ihave Hregs := Hrestore $$ %value Hcell
    iapply ih $$ Hcert Hregs Hcode Hfinish
  | @readMem rs n req word k Q ram plain allowed rest ih =>
    haveI : Persistent (TsoRead.pristineWindow capacity.era.heap.ledger era.timestamps req.pa n) := by
      unfold TsoRead.pristineWindow TsoRead.pristineByte Tso.timestampElem
      infer_instance
    rw [impure_bind_eq]
    iintro #Hcert Hregs Hcode Hfinish
    ihave ⟨Hbytes, #Hpristine, Hrestore⟩ := access.access n req word allowed $$ Hcode
    iapply memoryRules.pristine image fixed whole gen era cpu n req
      (fun result => k result >>= continuation) dq word post ram plain $$ Hcert Hbytes Hpristine
    iintro !> %view Hbytes Hview
    ihave Hcode := Hrestore $$ Hbytes Hpristine
    iapply ih $$ Hcert Hregs Hcode Hfinish

end MachCSL.Logic.EventPlan
