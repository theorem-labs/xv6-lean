import Xv6.Kernel.KptPublishBarrierDefs

namespace Xv6.Kernel.KptPublishBarrier
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

structure ProtocolSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  boot : ∀ era cpu ξ mapping tree, hartAgent cpu = 0 →
    iprop(⊢ BarrierWP.ghostStep capacity.machine.era era
      (input capacity era cpu ξ mapping tree) (published capacity era cpu ξ mapping tree .boot))
  view : ∀ era cpu ξ mapping tree, hartAgent cpu = 0 →
    iprop(⊢ BarrierWP.pubStep capacity.machine.era era cpu
      (input capacity era cpu ξ mapping tree) (published capacity era cpu ξ mapping tree .view))

structure ResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  install : ∀ era cpu ξ mapping tree route (N : Namespace) (E : CoPset) root,
    hartAgent cpu = 0 → KptShared.TreeSpec root mapping tree →
    iprop(published capacity era cpu ξ mapping tree route ⊢ |={E}=>
      output capacity era cpu ξ N root tree route)

/-- An actual barrier is the event site. No heap/TSO interpretation,
publication callback or replacement physical tree is a client premise. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  boot : ∀ image fixed whole gen era cpu ξ mapping tree (N : Namespace) root kind k post,
    hartAgent cpu = 0 → KptShared.TreeSpec root mapping tree →
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      input capacity era cpu ξ mapping tree -∗
      ▷ (output capacity era cpu ξ N root tree .boot -∗
        BarrierWP.threadWP capacity.machine image fixed whole (.hart gen cpu (k ())) post) -∗
      BarrierWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.barrier kind) k)) post)
  view : ∀ image fixed whole gen era cpu ξ mapping tree (N : Namespace) root kind k post,
    hartAgent cpu = 0 → KptShared.TreeSpec root mapping tree → fenceDrains kind = true →
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      input capacity era cpu ξ mapping tree -∗
      ▷ (output capacity era cpu ξ N root tree .view -∗
        BarrierWP.threadWP capacity.machine image fixed whole (.hart gen cpu (k ())) post) -∗
      BarrierWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.barrier kind) k)) post)

end Xv6.Kernel.KptPublishBarrier
