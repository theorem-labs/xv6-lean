import MachCSL.Logic.BarrierWPDefs

namespace MachCSL.Logic.BarrierWP
open Iris Iris.BI MachCSL.Machine

structure BarrierWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  ghost : ∀ image fixed whole gen era cpu kind k P Q post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      ghostStep capacity.era era P Q -∗ P -∗
      ▷ (Q -∗ threadWP capacity image fixed whole (.hart gen cpu (k ())) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.barrier kind) k)) post)
  publish : ∀ image fixed whole gen era cpu kind k P Q post,
    fenceDrains kind = true →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      pubStep capacity.era era cpu P Q -∗ P -∗
      ▷ (Q -∗ threadWP capacity image fixed whole (.hart gen cpu (k ())) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.barrier kind) k)) post)

end MachCSL.Logic.BarrierWP
