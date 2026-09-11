import Xv6.Kernel.KptFetchHalfReadProofs

namespace Xv6.Kernel.KptFetchHalf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem translated_read shares rs (config : Config rs) tier address ppn n (width : Supported n)
    (aligned : is_aligned_vaddr (.Virtaddr address) n = true) (text : KernelTextDatum.AddrIsText (KernelTextDatum.physical ppn address))
    (word : BitVec (8*n)) data tree p2 p1 a d branch
    image fixed whole gen era cpu N root rr (continuation : FetchBytes_Result n → SailM Unit) post
    (facts : KptAddress.OutcomeFacts rs data root address ppn .rx (.InstructionFetch ())
      (.translated tree p2 p1 a d branch)) :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      window capacity era tier address n .discard word -∗
      KernelTextDatum.physicalWindow capacity era (KernelTextDatum.physical ppn address) n .discard word -∗
      KernelTextDatum.pristineWindow capacity era (KernelTextDatum.physical ppn address) n -∗
      KptAddress.resources capacity era cpu rs shares N root data address ppn .rx rr
        (.translated tree p2 p1 a d branch) -∗
      ▷ (∀ view, resources capacity era cpu rs shares N root rr
          [⟨address,ppn,data,tree,p2,p1,a,d,branch,view⟩] -∗
        window capacity era tier address n .discard word -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.FetchBytes_Success word))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (afterTranslation n
          (KptAddress.result address ppn (.InstructionFetch ()) (.translated tree p2 p1 a d branch)) >>= continuation)) post) := by
  have success := translation_success rs root ⟨address,ppn,data,tree,p2,p1,a,d,branch,0⟩ config facts
  change KptAddress.result address ppn (.InstructionFetch ()) (.translated tree p2 p1 a d branch) = _ at success
  rw [success]
  unfold afterTranslation
  rw [BootPmp.sail_bind_assoc]
  iintro #Hcert #Hwindow Hphysical Hpristine Hresources Hfinish
  iunfold KptAddress.resources at Hresources
  icases Hresources with ⟨Haux,Hopened,_,Hresv,Hreceipts⟩
  iapply read_opened capacity shares rs
    (KptAddress.afterData rs data address ppn .rx (.translated tree p2 p1 a d branch)) config
    (KernelTextDatum.physical ppn address) n width text (physical_alignment address ppn n width aligned)
    image fixed whole gen era cpu N root word _ post $$ Hcert Haux Hopened Hphysical Hpristine
  iintro !> %view Haux Hresidue Hreceipt
  rw [BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view [Haux Hresidue Hresv Hreceipts Hreceipt] Hwindow
  unfold resources receipts receipt
  simp only [traceReservation,List.foldl_cons,List.foldl_nil,Step.afterReservation,Step.outcome]
  iframe Haux Hresidue Hresv
  simp only [BigSepL.bigSepL_cons.to_eq,BigSepL.bigSepL_nil.to_eq,sep_emp.to_eq]
  iframe Hreceipts Hreceipt

/-- Native shared translation, actual physical read and residue restoration.
The selected PPN and all physical bytes come from the supplied RX window. -/
theorem wp_fetch shares rs (config : Config rs) start address n (width : Supported n)
    (aligned : is_aligned_vaddr (.Virtaddr address) n = true) tier (word : BitVec (8*n))
    image fixed whole gen era cpu (N : Namespace) root rr
    (continuation : FetchBytes_Result n → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      window capacity era tier address n .discard word -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tier address n word rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program start address n >>= continuation)) post) := by
  have positive : 0 < n := by rcases width with rfl | rfl <;> decide
  iintro #Hcert Haux Hresidue #Hwindow Hresv Hfinish
  ihave ⟨%ppn,#Hclaims,Hphysical,#Hpristine,_⟩ :=
    KernelTextDatum.window_access capacity era tier address n .discard word positive (page address n width aligned) $$ Hwindow
  ihave #Hhead := KernelTextDatum.window_head capacity era tier address n ppn positive $$ Hclaims
  iunfold KernelTextDatum.claim at Hhead
  icases Hhead with ⟨#Hmap,%textFacts⟩
  ihave #Hmap' : KptShared.mapAt capacity era (Sv39Address.vpn address) ppn .rx $$ []
  · unfold KptShared.mapAt Sv39Address.vpn
    isimp only [KernelTextDatum.vpn,KernelDatum.vpn] at Hmap
    iexact Hmap
  have canonical : Sv39Address.Canonical address := KernelDatum.canonical address textFacts.1
  rw [factor, BootPmp.sail_bind_assoc]
  iapply (KptAddress.nativeSpec capacity).translate shares rs config.ambient address ppn .rx (.InstructionFetch ())
    KptLeaf.Supported.fetch (by rfl) (Or.inl rfl) image fixed whole gen era cpu N root rr
    (fun response => afterTranslation n response >>= continuation) post $$ Hcert Haux Hresidue Hmap' Hresv
  iunfold KptAddress.finish
  isimp only []
  isplit
  · iintro %data
    iunfold KptAddress.continueWith
    iintro %bad _
    exact False.elim (bad canonical)
  · iintro %data %tree %p2 %p1 %a %d %path
    iunfold finish at Hfinish
    iunfold guard at Hfinish
    ihave Hfinish := Hfinish $$ %ppn %data %tree %p2 %p1 %a %d %path
    isplit
    · ihave Hfinish := Iris.BI.and_elim_l $$ Hfinish
      iintro %ca %cd %update
      ihave Hfinish := Hfinish $$ %ca %cd %update
      cases update <;> simp only [KptAD.guarded]
      all_goals first | iintro !> !> | iintro !> | skip
      all_goals
        iunfold KptAddress.continueWith
        iintro %facts Hresources
        ihave Hfinish := Hfinish $$ %facts
        iapply translated_read capacity shares rs config tier address ppn n width aligned textFacts.2.1 word
          data tree p2 p1 a d _ image fixed whole gen era cpu N root rr continuation post facts
          $$ Hcert Hwindow Hphysical Hpristine Hresources Hfinish
    · ihave Hfinish := Iris.BI.and_elim_r $$ Hfinish
      iintro !> !> !> %ca %cd %v2 %v1 %v0 %update
      ihave Hfinish := Hfinish $$ %ca %cd %v2 %v1 %v0 %update
      cases update <;> simp only [KptAD.guarded]
      all_goals first | iintro !> !> | iintro !> | skip
      all_goals
        iunfold KptAddress.continueWith
        iintro %facts Hresources
        ihave Hfinish := Hfinish $$ %facts
        iapply translated_read capacity shares rs config tier address ppn n width aligned textFacts.2.1 word
          data tree p2 p1 a d _ image fixed whole gen era cpu N root rr continuation post facts
          $$ Hcert Hwindow Hphysical Hpristine Hresources Hfinish

theorem actual : Spec capacity := ⟨wp_fetch capacity⟩

end Xv6.Kernel.KptFetchHalf
