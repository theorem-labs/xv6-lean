import Xv6.Kernel.KptWriteEventUpdate

namespace Xv6.Kernel.KptWriteEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (ownership : KptOwnership.Spec capacity)
include ownership

/-- The native conditional rule derives held-snapshot readback and covers
blocked retry. Only its successful later opens the invariant for the update. -/
theorem wp_write image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0
    (mapped : PtTree.Maps tree vpn p2 p1 p0)
    (req : MemoryWriteWP.WriteRequest 8) (reserved new : BitVec 64)
    (location : req.pa = PtTree.addr0 p1 vpn) (present : req.value = some new)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true)
    (canonical : PteCanonical.canon new = PteCanonical.canon p0)
    (continuation : MemoryWriteWP.WriteResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
        (some (snapshot req.pa 8 reserved)) -∗
      ▷ (∀ time, ⌜0 < time⌝ -∗ clients capacity era N root tree -∗
        Tso.History.logElem capacity.machine.era.history era.logEntries (time - 1)
          ⟨snapshot req.pa 8 new, hartAgent cpu⟩ -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) time -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok none))) post) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.writeMem 8 req) continuation)) post) := by
  iintro Hcert #Hclients Hresv Hcontinue
  iapply MemoryWriteWP.wp_conditional capacity.machine (MemoryWriteWP.nativeContracts capacity.machine)
    image fixed whole gen era cpu 8 req reserved new continuation post present ram (by decide) $$ Hcert Hresv
  unfold MemoryWriteWP.conditionalPremise MemoryWriteWP.checkedPremise
  iintro %g %readReserved Hbundle Htso
  iapply fupd_mask_intro (E2 := ∅) (by intro x _; exact CoPset.mem_full)
  iintro Hback
  iintro !>
  imod Hback
  imod update capacity ownership era g cpu N ⊤ root tree vpn p2 p1 p0
    (by intro x _; exact CoPset.mem_full) mapped req new location canonical
    $$ Hclients Hbundle Htso with ⟨Hbundle,Htso,Hreceipt,_⟩
  imodintro
  iframe Hbundle Htso
  iintro Hresv Hview
  iapply Hcontinue $$ %(g.log.length+1) [] Hclients [Hreceipt] Hresv [Hview]
  · ipureintro; omega
  · simp only [Nat.add_sub_cancel]
    iexact Hreceipt
  · have postView : MemoryWriteWP.postView g cpu req = g.log.length+1 := by
      simp only [MemoryWriteWP.postView, exclusive, ↓reduceIte]
    rw [← postView]
    iexact Hview

theorem actual : Spec capacity := ⟨update capacity ownership, wp_write capacity ownership⟩

end Xv6.Kernel.KptWriteEvent
