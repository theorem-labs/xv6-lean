import MachCSL.Machine.SpinlockFamilyPlans
import MachCSL.Logic.EventPlanLink
import MachCSL.Logic.RestartWPLink
import MachCSL.Logic.SpinlockCodeProofs
import MachCSL.Logic.SpinlockProtocolLink

namespace MachCSL.Logic.SpinlockWP
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : SpinlockProtocol.Capacity GF)

theorem cycle (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (N : Namespace) (γ : GName) (cpu : CPU)
    (i : Fin 17) (rs : RegisterFile) (rr : Option Reservation) (phase : SpinlockProtocol.Phase)
    (tick : Bool) (dq : DFrac) (post : Empty → IProp GF)
    (family : SpinlockFamily.Family cpu i rs phase) :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      EventWP.ownedCells capacity.machine.era.registers (era.registers cpu) rs -∗
      SpinlockCode.allCode capacity.machine era dq -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      SpinlockProtocol.resource capacity fixed gen era N γ cpu phase -∗
      (∀ after rr' next, ⌜∃ j, SpinlockFamily.Family cpu j after next⌝ -∗
        EventWP.ownedCells capacity.machine.era.registers (era.registers cpu) after -∗
        SpinlockCode.allCode capacity.machine era dq -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr' -∗
        SpinlockProtocol.resource capacity fixed gen era N γ cpu next -∗
        DeadThread.threadWP capacity.machine SpinlockImage.image fixed whole (.hart gen cpu (.pure ())) post) -∗
      DeadThread.threadWP capacity.machine SpinlockImage.image fixed whole (.hart gen cpu (Machine.cycle tick)) post) := by
  have rule := (EventPlan.nativeEventPlanSpec (hlc := hlc) capacity.machine).fold
    (SpinlockFetch.CodeRead i) SpinlockProtocol.relations
    (SpinlockProtocol.resource capacity fixed gen era N γ cpu) dq
    (SpinlockCode.allCode capacity.machine era dq) era
    (SpinlockCode.codeAccess capacity.machine era dq i) SpinlockImage.image fixed whole gen cpu
    (SpinlockProtocol.access (hlc := hlc) capacity fixed gen era N γ cpu)
    rs rr phase (Machine.cycle tick) _ (fun value : Unit => pure value) post
    (SpinlockFamily.cycle_plan i family rr tick)
  simp only [EventPlan.sail_bind_pure_eq] at rule
  iintro Hcert Hregs Hcode Hresv Hphase Hfinish
  iapply rule $$ Hcert Hregs Hcode Hresv Hphase
  iintro %value %after %rr' %next %good Hregs Hcode Hresv Hphase
  cases value
  iapply Hfinish $$ %after %rr' %next [] Hregs Hcode Hresv Hphase
  ipureintro
  exact good

theorem loop (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (N : Namespace) (γ : GName) (cpu : CPU)
    (i : Fin 17) (rs : RegisterFile) (phase : SpinlockProtocol.Phase)
    (dq : DFrac) (post : Empty → IProp GF)
    (family : SpinlockFamily.Family cpu i rs phase) :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      EventWP.ownedCells capacity.machine.era.registers (era.registers cpu) rs -∗
      SpinlockCode.allCode capacity.machine era dq -∗
      Reservations.resvAny capacity.machine.era.reservations era.reservations cpu -∗
      SpinlockProtocol.resource capacity fixed gen era N γ cpu phase -∗
      DeadThread.threadWP capacity.machine SpinlockImage.image fixed whole (.hart gen cpu (.pure ())) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  have general : iprop(⊢ ∀ i : Fin 17, ∀ rs : RegisterFile, ∀ phase : SpinlockProtocol.Phase,
      ⌜SpinlockFamily.Family cpu i rs phase⌝ -∗
      MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      EventWP.ownedCells capacity.machine.era.registers (era.registers cpu) rs -∗
      SpinlockCode.allCode capacity.machine era dq -∗
      Reservations.resvAny capacity.machine.era.reservations era.reservations cpu -∗
      SpinlockProtocol.resource capacity fixed gen era N γ cpu phase -∗
      DeadThread.threadWP capacity.machine SpinlockImage.image fixed whole (.hart gen cpu (.pure ())) post) := by
    iloeb as IH
    iintro %index %file %stage %family #Hcert Hregs Hcode Hresv Hphase
    iapply (RestartWP.restartWPSpec capacity.machine).restart SpinlockImage.image fixed whole gen era cpu post $$ Hcert Hresv
    iintro !> %tick Hresv
    iapply cycle capacity fixed whole gen era N γ cpu index file none stage tick dq post family $$
      Hcert Hregs Hcode Hresv Hphase
    iintro %after %rr' %next %good Hregs Hcode Hresv Hphase
    obtain ⟨index', family'⟩ := good
    iapply IH $$ %index' %after %next [] Hcert Hregs Hcode [Hresv] Hphase
    · ipureintro; exact family'
    · unfold Reservations.resvAny
      iexists rr'
      iexact Hresv
  iintro Hcert Hregs Hcode Hresv Hphase
  iapply general $$ %i %rs %phase [] Hcert Hregs Hcode Hresv Hphase
  ipureintro
  exact family

end MachCSL.Logic.SpinlockWP
