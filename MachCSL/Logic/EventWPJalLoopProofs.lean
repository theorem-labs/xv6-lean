import MachCSL.Logic.EventWPJalLoopSpec

namespace MachCSL.Logic.EventWPJal
open Iris Iris.BI MachCSL.Machine

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_jal_loop (cycles : JalCycleWPSpec capacity) (restart : RestartWP.RestartWPSpec capacity)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile)
    (dq : DFrac) (post : Empty → IProp GF)
    (static : JalLoopPlan.Static rs) (covered : JalLoopPlan.SnapshotCovered cpu rs) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed generation era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  have general : iprop(⊢ ∀ rs : RegisterFile,
      ⌜JalLoopPlan.Static rs⌝ -∗ ⌜JalLoopPlan.SnapshotCovered cpu rs⌝ -∗
      MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) := by
    iloeb as IH
    iintro %file %hstatic %hcovered #Hcert Hregs Hcode Hresv
    iapply restart.restart image fixed whole generation era cpu post $$ Hcert Hresv
    iintro !> %tick Hresv
    iapply cycles.cycle image fixed whole generation era cpu file tick dq post hstatic hcovered $$
      Hcert Hregs Hcode
    iintro Hregs Hcode
    iapply IH $$ %(JalLoopPlan.cycleAfter tick file) [] [] Hcert Hregs Hcode [Hresv]
    · ipureintro; exact JalLoopPlan.static_cycle tick file hstatic
    · ipureintro; exact JalLoopPlan.snapshot_cycle cpu tick file hcovered
    · unfold Reservations.resvAny
      iexists none
      iexact Hresv
  iintro Hcert Hregs Hcode Hresv
  iapply general $$ %rs [] [] Hcert Hregs Hcode Hresv
  · ipureintro; exact static
  · ipureintro; exact covered

theorem jalLoopWPSpec (cycles : JalCycleWPSpec capacity) (restart : RestartWP.RestartWPSpec capacity) :
    JalLoopWPSpec capacity where
  loop := wp_jal_loop capacity cycles restart

end MachCSL.Logic.EventWPJal
