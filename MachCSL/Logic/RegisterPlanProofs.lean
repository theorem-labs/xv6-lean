import MachCSL.Logic.RegisterPlanSpec
import MachCSL.Logic.RegisterFootprintProofs
import MachCSL.Logic.RegisterWPProofs

namespace MachCSL.Logic.RegisterPlan
open Iris Iris.BI MachCSL.Machine RegisterFootprint

theorem Plan.bind {footprint : Footprint} {rs : RegisterFile} {program : SailM α}
    {next : α → SailM β} {P : α → RegisterFile → Prop} {Q : β → RegisterFile → Prop}
    (first : Plan footprint rs program P)
    (rest : ∀ value after, P value after → Plan footprint after (next value) Q) :
    Plan footprint rs (program >>= next) Q := by
  induction first with
  | pure good => exact rest _ _ good
  | read member _ ih => exact .read member (ih rest)
  | readAny _ ih => exact .readAny (fun value => ih value rest)
  | write member _ ih => exact .write member (ih rest)

theorem Plan.mono {footprint : Footprint} {rs : RegisterFile} {program : SailM α}
    {P Q : α → RegisterFile → Prop} (plan : Plan footprint rs program P)
    (imp : ∀ value after, P value after → Q value after) : Plan footprint rs program Q := by
  induction plan with
  | pure good => exact .pure (imp _ _ good)
  | read member _ ih => exact .read member (ih imp)
  | readAny _ ih => exact .readAny (fun value => ih value imp)
  | write member _ ih => exact .write member (ih imp)

theorem read_bind {A B : Type} (r : Register) (k : RegisterType r → SailM A)
    (next : A → SailM B) :
    ((Sail.ArchSem.FreeM.impure (.readReg r) k : SailM A) >>= next) =
      .impure (.readReg r) (fun value : RegisterType r => k value >>= next) := rfl

theorem write_bind {A B : Type} (r : Register) (value : RegisterType r) (k : Unit → SailM A)
    (next : A → SailM B) :
    ((Sail.ArchSem.FreeM.impure (.writeReg r value) k : SailM A) >>= next) =
      .impure (.writeReg r value) (fun value : Unit => k value >>= next) := rfl

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Native WP folding uses the proved single-register event rules directly.
Only finite footprint ownership is consumed and restored. -/
theorem fold {A : Type} (footprint : Footprint) (unique : Unique footprint)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (program : SailM A)
    (Q : A → RegisterFile → Prop) (continuation : A → SailM Unit) (post : Empty → IProp GF)
    (plan : Plan footprint rs program Q) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity.era.registers (era.registers cpu) rs footprint -∗
      (∀ value after, ⌜Q value after⌝ -∗
        cells capacity.era.registers (era.registers cpu) after footprint -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation value)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction plan with
  | @pure rs value Q good =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation value)) post)
    iintro #Hcert Hregs Hfinish
    iapply Hfinish $$ %value %rs [] Hregs
    ipureintro
    exact good
  | @read rs r dq k Q member rest ih =>
    rw [read_bind]
    iintro #Hcert Hregs Hfinish
    ihave ⟨Hcell, Hrestore⟩ := read_access capacity.era.registers (era.registers cpu)
      rs footprint r dq member $$ Hregs
    iapply RegisterWP.wp_read capacity image fixed whole gen era cpu r dq (rs r)
      (fun value => k value >>= continuation) post $$ Hcert Hcell
    iintro !> Hcell
    ihave Hregs := Hrestore $$ Hcell
    iapply ih $$ Hcert Hregs Hfinish
  | @readAny rs r k Q rest ih =>
    rw [read_bind]
    iintro #Hcert Hregs Hfinish
    iapply RegisterWP.wp_read_any capacity image fixed whole gen era cpu r
      (fun value => k value >>= continuation) post $$ Hcert
    iintro !> %value
    iapply ih value $$ Hcert Hregs Hfinish
  | @write rs r value k Q member rest ih =>
    rw [write_bind]
    iintro #Hcert Hregs Hfinish
    ihave ⟨Hcell, Hrestore⟩ := write_access capacity.era.registers (era.registers cpu)
      rs footprint r unique member $$ Hregs
    iapply RegisterWP.wp_write capacity image fixed whole gen era cpu r (rs r) value
      (fun result => k result >>= continuation) post $$ Hcert Hcell
    iintro !> Hcell
    ihave Hregs := Hrestore $$ %value Hcell
    iapply ih $$ Hcert Hregs Hfinish

theorem actual : Spec capacity := ⟨fold capacity⟩

end MachCSL.Logic.RegisterPlan
