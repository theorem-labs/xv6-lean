import MachCSL.Logic.EventWPJalSpec
import MachCSL.Logic.RestartWPSpec

namespace MachCSL.Logic.EventWPJal
open Iris Iris.BI MachCSL.Machine

/-- A native infinite per-hart loop under the explicit current PMP snapshot
family. This remains conditional on resources and is not all-power-on adequacy. -/
structure JalLoopWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  loop : ∀ image fixed whole generation era cpu rs dq post,
    JalLoopPlan.Static rs → JalLoopPlan.SnapshotCovered cpu rs →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗
      EventWP.codeResources capacity era dq -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post)

end MachCSL.Logic.EventWPJal
