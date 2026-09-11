import Xv6.Kernel.KptTreeWalkNodeProofs

namespace Xv6.Kernel.KptTreeWalk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

/-- Three actual ordinary reads, each opening and closing the shared tree.
The returned A/D pair comes from the final chosen view, not the snapshot. -/
theorem wp_walk shares rs tree vpn p2 p1 regions (config : Config rs tree vpn p2 p1 regions)
    ppn permission referenceA referenceD
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD))
    access (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    mxr doSum global image fixed whole gen era cpu (N : Namespace) root bound rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ a d view2 view1 view0,
        cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
        receipts capacity era cpu view2 view1 view0 -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok (output vpn p2 p1 ppn permission global a d, ())))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program tree vpn access mxr doSum global >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  obtain ⟨valid2,pointer2,valid1,pointer1⟩ := Sv39TreeWalk.mapped_pointers _ _ _ _ _ mapped
  have config2 : SupervisorPteRead.Config rs
      (KptReadEvent.address tree vpn p2 p1 ⟨2, by decide⟩) (regions 2) := by
    simpa only [Sv39TreeWalk.address, KptReadEvent.address] using config 2 (by decide)
  have config1 : SupervisorPteRead.Config rs
      (KptReadEvent.address tree vpn p2 p1 ⟨1, by decide⟩) (regions 1) := by
    simpa only [Sv39TreeWalk.address, KptReadEvent.address] using config 1 (by decide)
  iintro #Hcert Hregs Hclients Hresv Hfinish
  iunfold program
  iunfold Sv39TreeWalk.program
  iapply wp_pointer capacity shares rs tree vpn p2 p1 _ mapped ⟨2, by decide⟩ (by decide)
    (PtTree.base tree) p2 rfl rfl valid2 pointer2 (regions 2) config2
    access mxr doSum global image fixed whole gen era cpu N root bound rr continuation post
    $$ Hcert Hregs Hclients Hresv
  iintro !> %view2 Hregs Hclients Hresv Hview2
  iapply wp_pointer capacity shares rs tree vpn p2 p1 _ mapped ⟨1, by decide⟩ (by decide)
    (PtTree.nextBase p2) p1 rfl rfl valid1 pointer1 (regions 1) config1
    access mxr doSum (global || PtTree.globalBit p2) image fixed whole gen era cpu N root bound rr continuation post
    $$ Hcert Hregs Hclients Hresv
  iintro !> %view1 Hregs Hclients Hresv Hview1
  iapply wp_leaf capacity shares rs tree vpn p2 p1 ppn permission referenceA referenceD mapped
    (regions 0) (config 0 (by decide)) access supported allowed mxr doSum
    ((global || PtTree.globalBit p2) || PtTree.globalBit p1)
    image fixed whole gen era cpu N root bound rr continuation post $$ Hcert Hregs Hclients Hresv
  iintro !> %a %d %view0 Hregs Hclients Hresv Hview0
  rw [Sv39TreeWalk.output_eq]
  iapply Hfinish $$ %a %d %view2 %view1 %view0 Hregs Hclients Hresv [Hview2 Hview1 Hview0]
  iunfold receipts
  iunfold Sv39TreeWalk.receipts
  iunfold Sv39Walk.receipts
  iframe Hview2 Hview1 Hview0

theorem actual : Spec capacity := ⟨wp_pte capacity, wp_walk capacity⟩

end Xv6.Kernel.KptTreeWalk
