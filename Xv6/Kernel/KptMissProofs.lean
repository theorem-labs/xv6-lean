import Xv6.Kernel.KptMissFinishProofs
import Xv6.Kernel.KptADLink

namespace Xv6.Kernel.KptMiss
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

/-- Native shared walk, shared observed-word A/D update and actual TLB fill.
Every final pure fact is introduced only after the corresponding event guards. -/
theorem wp_miss shares rs asid tree vpn p2 p1 regions (config : Config rs tree vpn p2 p1 regions)
    ppn permission referenceA referenceD
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD))
    (coherent : TlbCoherence.Coherent asid tree (rs .tlb))
    access (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    mxr doSum image fixed whole gen era cpu (N : Namespace) root bound rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tree bound asid vpn p2 p1 ppn
        permission referenceA referenceD access rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program asid tree vpn access mxr doSum >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  rw [program_factor, BootPmp.sail_bind_assoc]
  iintro #Hcert Hregs #Hclients Hresv Hfinish
  iunfold finish at Hfinish
  ihave ⟨Hregs,Hrest⟩ := (cells_walk capacity era cpu rs shares).mp $$ Hregs
  iapply KptTreeWalk.wp_walk capacity shares.memory rs tree vpn p2 p1 regions config.walk
    ppn permission referenceA referenceD mapped access supported allowed mxr doSum false
    image fixed whole gen era cpu N root bound rr
    (fun walked => afterWalk asid vpn access mxr doSum walked >>= continuation) post
    $$ Hcert Hregs Hclients Hresv
  iintro !> !> !> %cachedA %cachedD %view2 %view1 %view0 Hregs _ Hresv Hwalk
  ihave Hregs := (cells_walk capacity era cpu rs shares).mpr $$ [Hregs Hrest]
  · iframe Hregs Hrest
  ihave ⟨Hregs,Htlb⟩ := (cells_ad capacity era cpu rs shares).mp $$ Hregs
  isimp only [after_walk, BootPmp.sail_bind_assoc]
  ihave Hadclients := clients_ad capacity era cpu N root tree bound $$ Hclients
  iapply KptAD.wp_update capacity shares rs (PtTree.addr0 p1 vpn) (regions 0) config.update
    N root tree vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD mapped rfl
    access supported allowed mxr doSum image fixed whole gen era cpu rr
    (fun updated => afterUpdate asid vpn (KptTreeWalk.output vpn p2 p1 ppn permission false cachedA cachedD)
      updated >>= continuation) post $$ Hcert Hregs Hadclients Hresv
  iunfold KptAD.finish
  iintro %branch
  ihave Hfinish := Hfinish $$ %cachedA %cachedD %view2 %view1 %view0 %branch
  cases branch <;> simp only [KptAD.guarded]
  all_goals first | iintro !> !> | iintro !> | skip
  all_goals
    iintro %facts Had
    iapply wp_finish capacity shares rs asid tree vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD
      access _ mapped coherent facts image fixed whole gen era cpu N root bound rr view2 view1 view0
      continuation post $$ Hcert Htlb Hclients Hwalk [Hfinish] Had
    iintro Hresources
    iapply Hfinish $$ %facts Hresources

end Xv6.Kernel.KptMiss
