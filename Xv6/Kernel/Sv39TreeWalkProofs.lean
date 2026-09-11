import Xv6.Kernel.Sv39TreeWalkNodeProofs
import Xv6.Kernel.Sv39WalkNodeProofs

namespace Xv6.Kernel.Sv39TreeWalk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Three actual ordinary reads along the source Maps path. The inert
reference leaf's A/D bits do not select the actual read's returned bits. -/
theorem wp_walk shares rs tree vpn p2 p1 regions (config : Config rs tree vpn p2 p1 regions)
    ppn permission referenceA referenceD
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD))
    access (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    mxr doSum global image fixed whole gen era cpu bound dq values rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.credential capacity era cpu bound -∗
      slots capacity era tree vpn p2 p1 ppn permission bound dq values -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ a d view2 view1 view0,
        cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
        slots capacity era tree vpn p2 p1 ppn permission bound dq values -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        receipts capacity era cpu view2 view1 view0 -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (output vpn p2 p1 ppn permission global a d, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program tree vpn access mxr doSum global >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  obtain ⟨valid2, pointer2, valid1, pointer1⟩ := mapped_pointers _ _ _ _ _ mapped
  iintro #Hcert Hregs Hcred Hslots Hresv Hfinish
  iunfold slots at Hslots
  icases Hslots with ⟨Hslot2, Hslot1, Hslot0⟩
  iunfold slot at Hslot2
  iunfold slot at Hslot1
  iunfold slot at Hslot0
  isimp only [address, reference, PtTree.addr2] at Hslot2
  isimp only [address, reference, PtTree.addr1] at Hslot1
  isimp only [address, reference, PtTree.addr0] at Hslot0
  iunfold program
  iapply wp_pointer capacity shares rs (PtTree.base tree) p2 valid2 pointer2 vpn ⟨2, by decide⟩ (by decide)
    (regions 2) (config 2 (by decide)) access mxr doSum global
    image fixed whole gen era cpu bound (dq 2) (values 2) rr continuation post
    $$ Hcert Hregs Hcred Hslot2 Hresv
  iintro !> %view2 Hregs Hcred Hslot2 Hresv Hview2
  iapply wp_pointer capacity shares rs (PtTree.nextBase p2) p1 valid1 pointer1 vpn ⟨1, by decide⟩ (by decide)
    (regions 1) (config 1 (by decide)) access mxr doSum (global || PtTree.globalBit p2)
    image fixed whole gen era cpu bound (dq 1) (values 1) rr continuation post
    $$ Hcert Hregs Hcred Hslot1 Hresv
  iintro !> %view1 Hregs Hcred Hslot1 Hresv Hview1
  have leaf := Sv39Walk.wp_leaf capacity shares rs (geometry tree p2 p1 ppn) vpn
    (regions 0) (config 0 (by decide)) permission access supported allowed mxr doSum
    ((global || PtTree.globalBit p2) || PtTree.globalBit p1)
    image fixed whole gen era cpu bound (dq 0) (values 0) rr continuation post
  simp only [show Sv39Walk.address (geometry tree p2 p1 ppn) vpn 0 = PtTree.addr0 p1 vpn from rfl,
    show (geometry tree p2 p1 ppn).leaf = ppn from rfl,
    show (geometry tree p2 p1 ppn).table0 = PtTree.nextBase p1 from rfl, PtTree.addr0] at leaf
  iapply leaf $$ Hcert Hregs Hcred Hslot0 Hresv
  iintro !> %a %d %view0 Hregs Hcred Hslot0 Hresv Hview0
  rw [output_eq]
  iapply Hfinish $$ %a %d %view2 %view1 %view0 Hregs Hcred [Hslot2 Hslot1 Hslot0]
    Hresv [Hview2 Hview1 Hview0]
  · iunfold slots
    iunfold slot
    simp only [address, reference, PtTree.addr2, PtTree.addr1, PtTree.addr0]
    iframe Hslot2 Hslot1 Hslot0
  · iunfold receipts
    iunfold Sv39Walk.receipts
    iframe Hview2 Hview1 Hview0

theorem actual : Spec capacity := ⟨wp_pointer capacity, wp_walk capacity⟩

end Xv6.Kernel.Sv39TreeWalk
