import MachCSL.Logic.EventWPJalUniversalSpec

namespace MachCSL.Logic.EventWPJal
open Iris Iris.BI MachCSL.Machine

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem universal_cycle_wp (events : EventWP.EventWPSpec capacity)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (tick : Bool)
    (dq : DFrac) (post : Empty → IProp GF) (family : JalLoopPlan.UniversalFamily rs) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      (EventWP.ownedCells capacity.era.registers (era.registers cpu) (JalLoopPlan.cycleAfter tick rs) -∗
        EventWP.codeResources capacity era dq -∗
        RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (Machine.cycle tick)) post) := by
  iintro Hcert Hregs Hcode Hfinish
  iapply events.fold JalLoopPlan.CodeRead dq (EventWP.codeResources capacity era dq) era
    (EventWP.codeRamAccess capacity era dq) image fixed whole generation cpu rs
    (Machine.cycle tick) _ post (JalLoopPlan.universal_cycle_plan tick rs family) $$
    Hcert Hregs Hcode
  iintro %after %good Hregs Hcode
  obtain ⟨_, rfl⟩ := good
  iapply Hfinish $$ Hregs Hcode

/-- Native guarded recursion covers all actual event successors and both restart
clock choices. Its family includes every arbitrary-preboot BootFacts witness. -/
theorem universal_loop_wp (events : EventWP.EventWPSpec capacity)
    (restart : RestartWP.RestartWPSpec capacity)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile)
    (dq : DFrac) (post : Empty → IProp GF) (family : JalLoopPlan.UniversalFamily rs) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed generation era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  have general : iprop(⊢ ∀ rs : RegisterFile, ⌜JalLoopPlan.UniversalFamily rs⌝ -∗
      MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) := by
    iloeb as IH
    iintro %file %hfamily #Hcert Hregs Hcode Hresv
    iapply restart.restart image fixed whole generation era cpu post $$ Hcert Hresv
    iintro !> %tick Hresv
    iapply universal_cycle_wp capacity events image fixed whole generation era cpu file tick dq post hfamily $$
      Hcert Hregs Hcode
    iintro Hregs Hcode
    iapply IH $$ %(JalLoopPlan.cycleAfter tick file) [] Hcert Hregs Hcode [Hresv]
    · ipureintro; exact JalLoopPlan.universalFamily_cycle tick file hfamily
    · unfold Reservations.resvAny
      iexists none
      iexact Hresv
  iintro Hcert Hregs Hcode Hresv
  iapply general $$ %rs [] Hcert Hregs Hcode Hresv
  ipureintro
  exact family

theorem universalJalWPSpec (events : EventWP.EventWPSpec capacity)
    (restart : RestartWP.RestartWPSpec capacity) : UniversalJalWPSpec capacity where
  cycle := universal_cycle_wp capacity events
  loop := universal_loop_wp capacity events restart

end MachCSL.Logic.EventWPJal
