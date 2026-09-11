import MachCSL.Logic.PowerWPDefs

namespace MachCSL.Logic.PowerWP
open Iris Iris.BI MachCSL.Machine

structure PowerWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  power : ∀ image fixed whole template N post,
    iprop(⊢ ObservationInvariant.trivial capacity.power N fixed.observations -∗
      bootHandler capacity image fixed whole template -∗
      DeadThread.threadWP capacity image fixed whole .power post)

end MachCSL.Logic.PowerWP
