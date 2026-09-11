import MachCSL.Logic.EventWPSpec
import MachCSL.Logic.EventWPCode
import MachCSL.Logic.RestartWPSpec
import MachCSL.Machine.JalLoopUniversal

namespace MachCSL.Logic.EventWPJal
open Iris Iris.BI MachCSL.Machine

/-- Actual fetched cycles and infinite restart loop under the family proved for
EVERY permitted JAL-image boot. Initial resources are explicit, not allocated here. -/
structure UniversalJalWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  cycle : ∀ image fixed whole generation era cpu rs tick dq post,
    JalLoopPlan.UniversalFamily rs →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      (EventWP.ownedCells capacity.era.registers (era.registers cpu) (JalLoopPlan.cycleAfter tick rs) -∗
        EventWP.codeResources capacity era dq -∗
        RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (Machine.cycle tick)) post)
  loop : ∀ image fixed whole generation era cpu rs dq post,
    JalLoopPlan.UniversalFamily rs →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post)

end MachCSL.Logic.EventWPJal
