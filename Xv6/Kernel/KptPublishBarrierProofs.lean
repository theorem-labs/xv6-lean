import Xv6.Kernel.KptPublishBarrierSpec
import Xv6.Kernel.KptPublishLink
import MachCSL.Logic.BarrierWPLink

namespace Xv6.Kernel.KptPublishBarrier
open Iris Iris.BI MachCSL.Machine MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem protocol_boot : ∀ era cpu ξ mapping tree, hartAgent cpu = 0 →
    iprop(⊢ BarrierWP.ghostStep capacity.machine.era era
      (input capacity era cpu ξ mapping tree) (published capacity era cpu ξ mapping tree .boot)) := by
  intro era cpu ξ mapping tree boot
  unfold BarrierWP.ghostStep input published
  iintro %g Hheap Htso ⟨Hrun, Htree, Hmap, Hunset, HboundUnset⟩
  have gate := (KptPublish.nativeSpec capacity).publish_boot era cpu ξ g 2 tree boot
  rw [show KptPublish.heapAt capacity era g = Era.heapInterpAt capacity.machine.era era g from rfl] at gate
  imod gate $$ Hheap Htso Hrun Htree with ⟨Hheap, Htso, Hrun, Htree, Hlog⟩
  imodintro
  iframe Hheap Htso
  iexists g.log.length
  iframe Hrun Htree Hlog Hmap Hunset HboundUnset
  unfold receipt
  itrivial

theorem protocol_view : ∀ era cpu ξ mapping tree, hartAgent cpu = 0 →
    iprop(⊢ BarrierWP.pubStep capacity.machine.era era cpu
      (input capacity era cpu ξ mapping tree) (published capacity era cpu ξ mapping tree .view)) := by
  intro era cpu ξ mapping tree boot
  unfold BarrierWP.pubStep input published
  iintro %g %drained _ Hheap Htso ⟨Hrun, Htree, Hmap, Hunset, HboundUnset⟩
  have gate := (KptPublish.nativeSpec capacity).publish_view era cpu ξ g 2 tree drained boot
  rw [show KptPublish.heapAt capacity era g = Era.heapInterpAt capacity.machine.era era g from rfl] at gate
  imod gate $$ Hheap Htso Hrun Htree with ⟨Hheap, Htso, Hrun, Htree, Hlog, Hview⟩
  imodintro
  iframe Hheap Htso
  iexists (g.views cpu)
  iframe Hrun Htree Hlog Hmap Hunset HboundUnset
  unfold receipt
  iexact Hview

variable {hlc : HasLC} [InvGS_gen hlc GF]

theorem install : ∀ era cpu ξ mapping tree route (N : Namespace) (E : CoPset) root,
    hartAgent cpu = 0 → KptShared.TreeSpec root mapping tree →
    iprop(published capacity era cpu ξ mapping tree route ⊢ |={E}=>
      output capacity era cpu ξ N root tree route) := by
  intro era cpu ξ mapping tree route N E root boot spec
  unfold published output
  iintro ⟨%B, Hrun, Htree, #Hlog, Hreceipt, Hmap, Hunset, HboundUnset⟩
  imod (KptShared.nativeSpec capacity).allocate era N E root mapping tree B spec
    $$ Htree Hmap Hlog Hunset HboundUnset with ⟨#Hshared, #Hsnapshot, #Hbound⟩
  imodintro
  iexists B
  iframe Hrun Hshared Hsnapshot Hbound Hlog Hreceipt
  unfold KptShared.credentials
  iexists B
  iframe Hbound
  have cred : iprop(⊢ KptPublish.logBound capacity era B -∗
      TsoPinnedReadWP.credential capacity.machine era cpu B) :=
    TsoPinnedRead.bootCredential_boot capacity.machine.era.tso era.tsoNames cpu B boot
  iapply cred $$ Hlog

variable [Platform]

private theorem fupd_thread image fixed whole e post :
    iprop((|={⊤}=> BarrierWP.threadWP capacity.machine image fixed whole e post) ⊢
      BarrierWP.threadWP capacity.machine image fixed whole e post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity.machine image fixed whole
  exact Iris.fupd_wp

theorem wp_boot : ∀ image fixed whole gen era cpu ξ mapping tree (N : Namespace) root kind k post,
    hartAgent cpu = 0 → KptShared.TreeSpec root mapping tree →
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      input capacity era cpu ξ mapping tree -∗
      ▷ (output capacity era cpu ξ N root tree .boot -∗
        BarrierWP.threadWP capacity.machine image fixed whole (.hart gen cpu (k ())) post) -∗
      BarrierWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.barrier kind) k)) post) := by
  intro image fixed whole gen era cpu ξ mapping tree N root kind k post boot spec
  iintro Hcert Hinput Hcontinue
  iapply BarrierWP.wp_ghost capacity.machine image fixed whole gen era cpu kind k
    (input capacity era cpu ξ mapping tree) (published capacity era cpu ξ mapping tree .boot) post
    $$ Hcert [] Hinput [Hcontinue]
  · iapply protocol_boot capacity era cpu ξ mapping tree boot
  · iintro !> Hpublished
    iapply fupd_thread capacity
    imod install capacity era cpu ξ mapping tree .boot N ⊤ root boot spec $$ Hpublished with Houtput
    iapply Hcontinue $$ Houtput

theorem wp_view : ∀ image fixed whole gen era cpu ξ mapping tree (N : Namespace) root kind k post,
    hartAgent cpu = 0 → KptShared.TreeSpec root mapping tree → fenceDrains kind = true →
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      input capacity era cpu ξ mapping tree -∗
      ▷ (output capacity era cpu ξ N root tree .view -∗
        BarrierWP.threadWP capacity.machine image fixed whole (.hart gen cpu (k ())) post) -∗
      BarrierWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.barrier kind) k)) post) := by
  intro image fixed whole gen era cpu ξ mapping tree N root kind k post boot spec drains
  iintro Hcert Hinput Hcontinue
  iapply BarrierWP.wp_publish capacity.machine image fixed whole gen era cpu kind k
    (input capacity era cpu ξ mapping tree) (published capacity era cpu ξ mapping tree .view) post drains
    $$ Hcert [] Hinput [Hcontinue]
  · iapply protocol_view capacity era cpu ξ mapping tree boot
  · iintro !> Hpublished
    iapply fupd_thread capacity
    imod install capacity era cpu ξ mapping tree .view N ⊤ root boot spec $$ Hpublished with Houtput
    iapply Hcontinue $$ Houtput

end Xv6.Kernel.KptPublishBarrier
