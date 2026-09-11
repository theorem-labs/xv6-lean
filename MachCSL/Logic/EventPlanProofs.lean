import MachCSL.Logic.EventPlanPrefix
import MachCSL.Machine.BootPmpProgram

namespace MachCSL.Logic.EventPlan
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]

theorem write_mode (capacity : MachineInterp.Capacity GF)
    (rules : MemoryWriteWP.MemoryWriteWPSpec capacity)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : WriteRequest n)
    (value : BitVec (8 * n)) (k : MemoryWriteWP.WriteResult → SailM Unit)
    (rr : Option Reservation) (mode : WriteMode n req rr) (post : Empty → IProp GF)
    (present : req.value = some value) (ram : deviceAddress req.pa = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      MemoryWriteWP.checkedPremise capacity image fixed whole gen era cpu n req value k (WriteFact mode) post -∗
      DeadThread.threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post) := by
  cases mode with
  | ordinary => exact rules.write image fixed whole gen era cpu n req value k rr post present ram
  | reserved old snapshot bound =>
    subst rr
    exact rules.conditional image fixed whole gen era cpu n req old value k post present ram bound

theorem fold_plan (facts : EventWP.InitialMapFacts) (capacity : MachineInterp.Capacity GF)
    (rules : Contracts capacity) {S A : Type} (reads : EventWP.ReadAllowed)
    (rel : Relations S) (R : S → IProp GF) (dq : DFrac) (code : IProp GF) (era : Era.Record)
    (codeAccess : EventWP.RamAccess capacity era reads dq code)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (cpu : CPU) (access : Access capacity fixed gen era cpu rel R)
    (rs : RegisterFile) (rr : Option Reservation) (s : S) (program : SailM A)
    (Q : A → RegisterFile → Option Reservation → S → Prop)
    (continuation : A → SailM Unit) (post : Empty → IProp GF)
    (plan : Plan reads rel rs rr s program Q) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗ code -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗ R s -∗
      (∀ value after rr' next, ⌜Q value after rr' next⌝ -∗
        EventWP.ownedCells capacity.era.registers (era.registers cpu) after -∗ code -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr' -∗ R next -∗
        DeadThread.threadWP capacity image fixed whole (.hart gen cpu (continuation value)) post) -∗
      DeadThread.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction plan with
  | @pure rs rr s value Q good =>
    rw [pure_bind_eq]
    iintro #Hcert Hregs Hcode Hresv HR Hfinish
    iapply Hfinish $$ %value %rs %rr %s [] Hregs Hcode Hresv HR
    ipureintro
    exact good
  | @«prefix» B rs rr s program next P Q first rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hcode Hresv HR Hfinish
    iapply fold_bind facts capacity rules.registers rules.plain reads dq code era codeAccess
      image fixed whole gen cpu rs program P (fun value => next value >>= continuation) post first $$
      Hcert Hregs Hcode
    iintro %value %after %good Hregs Hcode
    iapply ih value after good $$ Hcert Hregs Hcode Hresv HR Hfinish
  | @plain rs rr s n req k Q enabled ram kind rest ih =>
    rw [readMem_bind_eq]
    iintro #Hcert Hregs Hcode Hresv HR Hfinish
    iapply rules.plain.plain image fixed whole gen era cpu n req
      (fun value => k value >>= continuation) (PlainAllowed rel s n req) post ram kind $$ Hcert
    iunfold MemoryReadWP.plainPremise
    iintro %g %live Hpower
    imod access.plain s n req enabled $$ HR %g [] Hpower with ⟨%total, Hclose⟩
    · ipureintro; exact live
    imodintro
    iframe %total
    iintro !>
    imod Hclose with ⟨Hpower, Hnext⟩
    imodintro
    iframe Hpower
    iintro %view %word %lower %upper %read %allowed Hview
    ihave ⟨%next, %step, HR⟩ := Hnext $$ %view %word [] [] [] [] Hview
    · ipureintro; exact lower
    · ipureintro; exact upper
    · ipureintro; exact read
    · ipureintro; exact allowed
    iapply ih word next step $$ Hcert Hregs Hcode Hresv HR Hfinish
  | @exclusive rs rr s n req k Q enabled ram kind rest ih =>
    rw [readMem_bind_eq]
    iintro #Hcert Hregs Hcode Hresv HR Hfinish
    iapply rules.exclusive.exclusive image fixed whole gen era cpu n req
      (fun value => k value >>= continuation) rr post ram kind $$ Hcert Hresv
    iunfold MemoryExclusiveWP.exclusivePremise
    iintro %g Hbundle Htso Hview
    imod access.exclusive s n req enabled $$ HR %g Hbundle Htso Hview with ⟨%word, %read, Hclose⟩
    imodintro
    iexists word
    iframe %read
    iintro !>
    imod Hclose with ⟨Hbundle, Htso, %next, %step, HR⟩
    imodintro
    iframe Hbundle Htso
    iintro Hresv
    iapply ih word next step $$ Hcert Hregs Hcode Hresv HR Hfinish
  | @write rs rr s n req value k Q enabled present ram mode eligible rest ih =>
    change MemoryWriteWP.WriteResult → SailM A at k
    rw [writeMem_bind_eq]
    have finish : iprop(⊢ R s -∗
        (∀ next, ⌜rel.write s n req value next⌝ -∗
          Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗ R next -∗
          DeadThread.threadWP capacity image fixed whole
            (.hart gen cpu (k (.Ok none) >>= continuation)) post) -∗
        MemoryWriteWP.checkedPremise capacity image fixed whole gen era cpu n req value
          (fun result => k result >>= continuation) (WriteFact mode) post) := by
      unfold MemoryWriteWP.checkedPremise
      iintro HR Hfinish %g %fact Hbundle Htso
      imod access.write s rr n req value mode enabled eligible $$ HR %g [] Hbundle Htso with Hclose
      · ipureintro; exact fact
      imodintro
      iintro !>
      imod Hclose with ⟨Hbundle, Htso, Hnext⟩
      imodintro
      iframe Hbundle Htso
      iintro Hresv Hview
      ihave ⟨%next, %step, HR⟩ := Hnext $$ Hview
      iapply Hfinish $$ %next [] Hresv HR
      ipureintro
      exact step
    iintro #Hcert Hregs Hcode Hresv HR Hfinish
    ihave Hcallback := finish $$ HR [Hregs Hcode Hfinish]
    · iintro %next %step Hresv HR
      iapply ih next step $$ Hcert Hregs Hcode Hresv HR Hfinish
    iapply write_mode capacity rules.write image fixed whole gen era cpu n req value
      (fun result => k result >>= continuation) rr mode post present ram $$ Hcert Hresv Hcallback
  | @barrier rs rr s kind k Q enabled rest ih =>
    rw [impure_bind_eq]
    iintro #Hcert Hregs Hcode Hresv HR Hfinish
    iapply rules.barrier.ghost image fixed whole gen era cpu kind
      (fun result => k result >>= continuation) (R s)
      (iprop(∃ next, ⌜rel.barrier s kind next⌝ ∗ R next)) post $$ Hcert [] HR
    · iapply access.barrier s kind enabled
    iintro !> ⟨%next, %step, HR⟩
    iapply ih next step $$ Hcert Hregs Hcode Hresv HR Hfinish

theorem eventPlanSpec (facts : EventWP.InitialMapFacts) (capacity : MachineInterp.Capacity GF)
    (rules : Contracts capacity) : EventPlanSpec capacity where
  prefixBind := fold_bind facts capacity rules.registers rules.plain
  fold := fold_plan facts capacity rules

end MachCSL.Logic.EventPlan
