import Xv6.Kernel.KptFetchGuardProofs

namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

/-- Every accepted plan chunk is discharged by the actual native half-fetch;
register prefixes, residue updates, reservation changes and receipts compose. -/
theorem fold {α : Type} shares rs (config : Config rs) {parts : List Chunk}
    {program : SailM α} {value : α} (plan : Plan (footprint shares) rs parts program value)
    tier image fixed whole gen era cpu (N : Namespace) root rr
    (continuation : α → SailM Unit) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      chunkWindows capacity era tier parts -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      guardChunks rs root (parts.map Chunk.address) (fun trace => iprop(
        runResources capacity era cpu rs shares N root rr trace -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation value)) post)) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction plan generalizing rr with
  | pure value =>
    simp only [List.map_nil,guardChunks,List.foldr_nil,BootPmp.sail_pure_bind]
    iintro #Hcert Hcells Hresidue _ Hresv Hfinish
    iapply Hfinish $$ [Hcells Hresidue Hresv]
    iunfold runResources
    isimp only [KptFetchHalf.traceReservation,List.foldl_nil,KptFetchHalf.receipts,
      BigSepL.bigSepL_nil.to_eq,sep_emp.to_eq]
    iframe Hcells Hresidue Hresv
  | @«prefix» β segment value next result parts first rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hcells Hresidue Hwindows Hresv Hfinish
    iapply RegisterPlan.fold capacity.machine (footprint shares) (unique shares)
      image fixed whole gen era cpu rs segment _ (fun value => next value >>= continuation) post first
      $$ Hcert Hcells
    iintro %got %after %equal Hcells
    rcases equal with ⟨rfl,rfl⟩
    iapply ih rr $$ Hcert Hcells Hresidue Hwindows Hresv Hfinish
  | @chunk part next result parts width aligned rest ih =>
    rw [BootPmp.sail_bind_assoc]
    simp only [List.map_cons,guardChunks_cons]
    iintro #Hcert Hcells Hresidue Hwindows Hresv Hfinish
    iunfold chunkWindows at Hwindows
    isimp only [BigSepL.bigSepL_cons.to_eq] at Hwindows
    icases Hwindows with ⟨#Hwindow,Hwindows⟩
    ihave ⟨Hhead,Haux⟩ := (partition capacity era cpu rs shares).mp $$ Hcells
    iapply KptFetchHalf.wp_fetch capacity shares.translation rs config.translation part.start part.address
      part.width width aligned tier part.word image fixed whole gen era cpu N root rr
      (fun response => next response >>= continuation) post $$ Hcert Haux Hresidue Hwindow Hresv
    iunfold KptFetchHalf.finish
    iapply guard_mono $$ [Hhead Hwindows] Hfinish
    iintro %step Hrest Hhalf _
    iunfold KptFetchHalf.resources at Hhalf
    icases Hhalf with ⟨Haux,Hresidue,Hresv,Hfirst⟩
    ihave Hcells := (partition capacity era cpu rs shares).mpr $$ [Hhead Haux]
    · iframe Hhead Haux
    ihave Hwindows' : chunkWindows capacity era tier parts $$ [Hwindows]
    · unfold chunkWindows; iexact Hwindows
    isimp only [KptFetchHalf.traceReservation,List.foldl_cons,List.foldl_nil] at Hresv
    iapply ih (step.afterReservation rr) $$ Hcert Hcells Hresidue Hwindows' Hresv
    iapply guardChunks_mono $$ [Hfirst] Hrest
    iintro %trace Hdone Hresources
    iunfold runResources at Hresources
    icases Hresources with ⟨Hcells,Hresidue,Hresv,Hreceipts⟩
    iapply Hdone $$ [Hcells Hresidue Hresv Hfirst Hreceipts]
    iunfold runResources
    isimp only [KptFetchHalf.traceReservation,List.foldl_cons,KptFetchHalf.receipts,
      BigSepL.bigSepL_cons.to_eq,BigSepL.bigSepL_nil.to_eq,sep_emp.to_eq] at Hfirst
    isimp only [KptFetchHalf.traceReservation,List.foldl_cons,KptFetchHalf.receipts,
      BigSepL.bigSepL_cons.to_eq,BigSepL.bigSepL_nil.to_eq,sep_emp.to_eq]
    isimp only [KptFetchHalf.traceReservation] at Hresv
    isimp only [KptFetchHalf.receipts] at Hreceipts
    iframe Hcells Hresidue Hresv Hfirst Hreceipts

end Xv6.Kernel.KptFetch
