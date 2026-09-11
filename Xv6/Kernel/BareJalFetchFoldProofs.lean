import Xv6.Kernel.BareJalFetchGuardProofs
import Xv6.Kernel.KptFetchWindowProofs

namespace Xv6.Kernel.BareJalFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem fold {α : Type} shares rs (config : Config rs) {chunks : List Chunk}
    {program : SailM α} {value : α} (plan : Plan (footprint shares) rs chunks program value)
    image fixed whole gen era cpu ξ (continuation : α → SailM Unit) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ -∗
      KptFetch.chunkWindows capacity era .identity chunks -∗
      guardReads (chunks.map KptFetch.Chunk.address) (fun views => iprop(
        cells capacity era cpu rs shares ∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ ∗
        receipts capacity era cpu views -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation value)) post)) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction plan with
  | pure value =>
    simp only [List.map_nil,guardReads,List.foldr_nil,BootPmp.sail_pure_bind]
    iintro #Hcert Hcells Hrun _ Hfinish
    iapply Hfinish $$ [Hcells Hrun]
    isimp only [receipts,BigSepL.bigSepL_nil.to_eq,sep_emp.to_eq]
    iframe
  | @«prefix» β segment value next result parts first rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hcells Hrun Hwindows Hfinish
    iunfold cells at Hcells
    iapply RegisterPlan.fold capacity.machine (footprint shares) (unique shares)
      image fixed whole gen era cpu rs segment _ (fun value => next value >>= continuation) post first $$ Hcert Hcells
    iintro %got %after %equal Hcells
    rcases equal with ⟨rfl,rfl⟩
    ihave Hcells' : cells capacity era cpu _ shares $$ [Hcells]
    · unfold cells; iexact Hcells
    iapply ih $$ Hcert Hcells' Hrun Hwindows Hfinish
  | @chunk part next result parts width aligned rest ih =>
    rw [BootPmp.sail_bind_assoc]
    simp only [List.map_cons,guardReads_cons]
    iintro #Hcert Hcells Hrun Hwindows Hfinish
    iunfold KptFetch.chunkWindows at Hwindows
    isimp only [BigSepL.bigSepL_cons.to_eq] at Hwindows
    icases Hwindows with ⟨#Hwindow,Hwindows⟩
    have gate := wp_chunk capacity shares rs config part.start part.address part.width width aligned
      image fixed whole gen era cpu ξ part.word (fun response => next response >>= continuation) post
    simp only [SupervisorBareFetch.program] at gate
    simp only [KptFetchHalf.program]
    iapply gate $$ Hcert Hcells Hrun Hwindow
    iintro !> %view Hcells Hrun _ Hfirst
    ihave Hrest := Hfinish $$ %view
    ihave Hwindows' : KptFetch.chunkWindows capacity era .identity parts $$ [Hwindows]
    · unfold KptFetch.chunkWindows; iexact Hwindows
    iapply ih $$ Hcert Hcells Hrun Hwindows'
    iapply guardReads_mono $$ [Hfirst] Hrest
    iintro %views Hdone ⟨Hcells,Hrun,Hreceipts⟩
    iapply Hdone $$ [Hcells Hrun Hfirst Hreceipts]
    isimp only [receipts] at Hreceipts
    isimp only [receipts,BigSepL.bigSepL_cons.to_eq]
    iframe

theorem wp_fetch shares rs (config : Config rs) word image fixed whole gen era cpu ξ continuation post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ -∗
      code capacity era (rs .PC) word -∗
      finish capacity image fixed whole gen era cpu ξ rs shares word continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hcells Hrun #Hcode Hfinish
  ihave Hbytes : KptFetch.instrBytes capacity era .identity (rs .PC) (.F_Base word) $$ []
  · iunfold code at Hcode; iexact Hcode
  ihave ⟨%selected,%facts,Hwindows⟩ := KptFetch.select_word capacity era .identity (rs .PC) (.F_Base word) $$ Hbytes
  rcases facts with ⟨equal,aligned⟩
  iapply fold capacity shares rs config (fetch_plan shares rs config.compressed aligned selected)
    image fixed whole gen era cpu ξ continuation post $$ Hcert Hcells Hrun Hwindows
  rw [KptFetch.parts_addresses,equal]
  iunfold finish at Hfinish
  iunfold guards at Hfinish
  ieval (change _ ⊢ guardReads (KptFetch.chunks (rs .PC) (.F_Base 0#32)) _)
  iapply guardReads_mono $$ [] Hfinish
  iintro %views Hdone ⟨Hcells,Hrun,Hreceipts⟩
  iapply Hdone
  iunfold resources
  iframe Hcells Hrun Hcode Hreceipts

theorem actual : Spec capacity := ⟨wp_chunk capacity,wp_fetch capacity⟩

end Xv6.Kernel.BareJalFetch
