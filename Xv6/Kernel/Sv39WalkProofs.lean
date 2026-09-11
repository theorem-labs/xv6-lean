import Xv6.Kernel.Sv39WalkNodeProofs

namespace Xv6.Kernel.Sv39Walk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- The complete three-level generated walk, with every actual read's native
resources and receipt retained through the genuine final continuation. -/
theorem wp_walk shares rs path vpn regions (config : Config rs path vpn regions)
    permission access (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    mxr doSum global image fixed whole gen era cpu bound dq values rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.credential capacity era cpu bound -∗
      slots capacity era path vpn permission bound dq values -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ a d view2 view1 view0,
        cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
        slots capacity era path vpn permission bound dq values -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        receipts capacity era cpu view2 view1 view0 -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (output path vpn permission global a d, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program path vpn access mxr doSum global >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hregs Hcred Hslots Hresv Hfinish
  iunfold slots at Hslots
  icases Hslots with ⟨Hslot2, Hslot1, Hslot0⟩
  iunfold slot at Hslot2
  iunfold slot at Hslot1
  iunfold slot at Hslot0
  isimp only [address, base, reference] at Hslot2
  isimp only [address, base, reference] at Hslot1
  isimp only [reference] at Hslot0
  iunfold program
  iapply wp_pointer capacity shares rs path.root path.table1 vpn ⟨2, by decide⟩ (by decide)
    (regions 2) (config 2 (by decide)) access mxr doSum global
    image fixed whole gen era cpu bound (dq 2) (values 2) rr continuation post
    $$ Hcert Hregs Hcred Hslot2 Hresv
  iintro !> %view2 Hregs Hcred Hslot2 Hresv Hview2
  iapply wp_pointer capacity shares rs path.table1 path.table0 vpn ⟨1, by decide⟩ (by decide)
    (regions 1) (config 1 (by decide)) access mxr doSum global
    image fixed whole gen era cpu bound (dq 1) (values 1) rr continuation post
    $$ Hcert Hregs Hcred Hslot1 Hresv
  iintro !> %view1 Hregs Hcred Hslot1 Hresv Hview1
  iapply wp_leaf capacity shares rs path vpn (regions 0) (config 0 (by decide))
    permission access supported allowed mxr doSum global
    image fixed whole gen era cpu bound (dq 0) (values 0) rr continuation post
    $$ Hcert Hregs Hcred Hslot0 Hresv
  iintro !> %a %d %view0 Hregs Hcred Hslot0 Hresv Hview0
  isimp only [address, base] at Hslot0
  iapply Hfinish $$ %a %d %view2 %view1 %view0 Hregs Hcred [Hslot2 Hslot1 Hslot0] Hresv [Hview2 Hview1 Hview0]
  · iunfold slots
    iunfold slot
    simp only [address, base, reference]
    iframe Hslot2 Hslot1 Hslot0
  · iunfold receipts
    iframe Hview2 Hview1 Hview0

theorem actual : Spec capacity := ⟨wp_walk capacity⟩

end Xv6.Kernel.Sv39Walk
