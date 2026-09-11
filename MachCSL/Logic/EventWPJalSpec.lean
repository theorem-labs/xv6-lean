import MachCSL.Logic.EventWPSpec
import MachCSL.Logic.EventWPCode
import MachCSL.Machine.JalLoopPlanLink

namespace MachCSL.Logic.EventWPJal
open Iris Iris.BI MachCSL.Machine

/-- One actual fetched cycle, keeping the terminal restart-node continuation.
The explicit snapshot premise is still stronger than arbitrary BootFacts. -/
structure JalCycleWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  cycle : ∀ image fixed whole generation era cpu rs tick dq post,
    JalLoopPlan.Static rs → JalLoopPlan.SnapshotCovered cpu rs →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      (EventWP.ownedCells capacity.era.registers (era.registers cpu) (JalLoopPlan.cycleAfter tick rs) -∗
        EventWP.codeResources capacity era dq -∗
        RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (Machine.cycle tick)) post)

end MachCSL.Logic.EventWPJal
