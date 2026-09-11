import MachCSL.Logic.RestartWPDefs

namespace MachCSL.Logic.RestartWP
open Iris Iris.BI MachCSL.Machine

structure RestartWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  restart : ∀ image fixed whole generation era cpu post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      ▷ (∀ tick : Bool, Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        DeadThread.threadWP capacity image fixed whole (.hart generation cpu (cycle tick)) post) -∗
      DeadThread.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post)

end MachCSL.Logic.RestartWP
