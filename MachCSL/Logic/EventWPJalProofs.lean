import MachCSL.Logic.EventWPJalSpec

namespace MachCSL.Logic.EventWPJal
open Iris Iris.BI MachCSL.Machine

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem fetched_cycle_wp (rules : EventWP.EventWPSpec capacity)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (tick : Bool)
    (dq : DFrac) (post : Empty → IProp GF)
    (static : JalLoopPlan.Static rs) (covered : JalLoopPlan.SnapshotCovered cpu rs) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      (EventWP.ownedCells capacity.era.registers (era.registers cpu) (JalLoopPlan.cycleAfter tick rs) -∗
        EventWP.codeResources capacity era dq -∗
        RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (Machine.cycle tick)) post) := by
  iintro Hcert Hregs Hram Hfinish
  iapply rules.fold JalLoopPlan.CodeRead dq (EventWP.codeResources capacity era dq) era
    (EventWP.codeRamAccess capacity era dq) image fixed whole generation cpu rs
    (Machine.cycle tick) _ post (JalLoopPlan.fetched_cycle_plan cpu tick rs static covered) $$
    Hcert Hregs Hram
  iintro %after %good Hregs Hram
  obtain ⟨_, rfl⟩ := good
  iapply Hfinish $$ Hregs Hram

theorem jalCycleWPSpec (rules : EventWP.EventWPSpec capacity) : JalCycleWPSpec capacity where
  cycle := fetched_cycle_wp capacity rules

end MachCSL.Logic.EventWPJal
