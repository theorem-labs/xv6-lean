import Xv6.Kernel.KptAddressResources
import Xv6.Kernel.KptHardwareLink
import Xv6.Kernel.Sv39AddressLink

namespace Xv6.Kernel.KptAddress
open Iris Iris.BI Iris.ProgramLogic MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

private theorem fupd_thread image fixed whole e post :
    iprop((|={⊤}=> MemoryReadWP.threadWP capacity.machine image fixed whole e post) ⊢
      MemoryReadWP.threadWP capacity.machine image fixed whole e post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity.machine image fixed whole
  exact fupd_wp

theorem translated_tail shares rs data root address ppn permission access
    (supported : KptLeaf.Supported access) tree p2 p1 a d bound rr branch
    (canonical : Sv39Address.Canonical address)
    (path : Path rs data root address ppn permission tree p2 p1 a d)
    (facts : KptTranslate.BranchFacts (prepare rs data) 0#16 (Sv39Address.vpn address)
      p2 p1 ppn permission a d access branch)
    image fixed whole gen era cpu N (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      Sv39Address.cells capacity.machine era cpu (prepare rs data) (outerShares shares) -∗
      KptShared.mapAt capacity era (Sv39Address.vpn address) ppn permission -∗
      KptTranslate.resources capacity era cpu (prepare rs data) (innerShares shares) N root tree bound
        0#16 (Sv39Address.vpn address) p2 p1 ppn permission rr branch -∗
      continueWith capacity image fixed whole gen era cpu rs shares N root data address ppn permission
        access rr continuation post (.translated tree p2 p1 a d branch) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (Sv39Address.resume address access (KptTranslate.result ppn branch) >>= continuation)) post) := by
  iintro #Hcert Houter Hmap Htranslated Hnext
  iapply (Sv39Address.nativeSpec capacity.machine).suffix address access supported
    (KptTranslate.result ppn branch) image fixed whole gen era cpu continuation post $$ Hcert
  iunfold continueWith at Hnext
  isimp only [result] at Hnext
  iapply Hnext $$ %⟨canonical,path,facts⟩ [Houter Hmap Htranslated]
  iapply return_translated capacity era cpu rs shares N root data address ppn permission tree p2 p1 a d bound rr branch
    path.rooted path.tor $$ Houter Hmap Htranslated

/-- All four hidden values are borrowed from the actual source residue.
Noncanonical and canonical paths use the same exact nine-cell partition. -/
theorem wp_translate shares rs (ambient : Ambient rs) address ppn permission access
    (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    (effectiveGiven : Sv39Address.Effective rs access)
    image fixed whole gen era cpu (N : Namespace) root rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      auxiliaryCells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      KptShared.mapAt capacity era (Sv39Address.vpn address) ppn permission -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root address ppn permission access rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program address access >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Haux Hresidue #Hmap Hresv Hfinish
  ihave ⟨%data,Hopened⟩ := open_residue capacity era cpu rs N root $$ Hresidue
  iunfold opened at Hopened
  icases Hopened with ⟨Hdata,%rooted,Hsnapshot,%tor,#Hshared,Hcredential⟩
  ihave Hcells := (partition capacity era cpu rs shares data).mpr $$ [Haux Hdata]
  · iframe Haux Hdata
  ihave ⟨Houter,Hinner⟩ := (split_cells capacity era cpu (prepare rs data) shares).mp $$ Hcells
  iunfold finish at Hfinish
  isimp only [] at Hfinish
  by_cases canonical : Sv39Address.Canonical address
  · ihave Hfinish := Iris.BI.and_elim_r $$ Hfinish
    iunfold KptResidue.tlbSnapOK at Hsnapshot
    icases Hsnapshot with ⟨%tree,%coherent,#Hsnapshot⟩
    iunfold KptShared.credentials at Hcredential
    icases Hcredential with ⟨%bound,#Hbound,#Hcredential⟩
    iapply fupd_thread capacity image fixed whole
    imod (KptHardware.nativeSpec capacity).mapped (prepare rs data) (controls rs data ambient tor)
      era N ⊤ root tree (Sv39Address.vpn address) ppn permission
      (by intro x _; exact CoPset.mem_full) $$ Hshared Hsnapshot Hmap with %hardware
    imodintro
    obtain ⟨base,p2,p1,a,d,mapped,config⟩ := hardware
    have path : Path rs data root address ppn permission tree p2 p1 a d :=
      ⟨rooted,tor,base,mapped,coherent⟩
    have outerConfig : Sv39Address.Config (prepare rs data) (PtTree.base tree) := by
      rw [base]; exact outer rs data root ambient rooted
    ihave Hfinish := Hfinish $$ %data %tree %p2 %p1 %a %d %⟨canonical,path⟩
    iapply (Sv39Address.nativeSpec capacity.machine).canonical (outerShares shares) (prepare rs data) tree
      outerConfig address access supported (effective rs data access effectiveGiven) canonical
      image fixed whole gen era cpu continuation post $$ Hcert Houter
    iintro Houter
    iapply (KptTranslate.nativeSpec capacity).translate (innerShares shares) (prepare rs data) 0#16 tree
      (Sv39Address.vpn address) p2 p1 KptHardware.regions config ppn permission a d mapped
      (by simpa using coherent) access supported allowed (Sv39Address.mxr (prepare rs data))
      (Sv39Address.doSum (prepare rs data)) image fixed whole gen era cpu N root bound rr
      (fun response => Sv39Address.resume address access response >>= continuation) post
      $$ Hcert Hinner [Hshared Hsnapshot Hbound Hcredential] Hresv
    · iunfold KptTranslate.clients
      iunfold KptMiss.clients
      iunfold KptTreeWalk.clients
      iframe Hshared Hsnapshot Hbound Hcredential
    · iunfold KptTranslate.finish
      isimp only []
      isplit
      · ihave Hfinish := Iris.BI.and_elim_l $$ Hfinish
        iintro %cachedA %cachedD %update
        ihave Hfinish := Hfinish $$ %cachedA %cachedD %update
        cases update <;> simp only [KptAD.guarded]
        all_goals first | iintro !> !> | iintro !> | skip
        all_goals
          iunfold KptTranslate.continueWith
          iintro %facts Htranslated
          iapply translated_tail capacity shares rs data root address ppn permission access supported tree p2 p1 a d bound rr _
            canonical path facts image fixed whole gen era cpu N continuation post
            $$ Hcert Houter Hmap Htranslated Hfinish
      · ihave Hfinish := Iris.BI.and_elim_r $$ Hfinish
        iintro !> !> !> %cachedA %cachedD %view2 %view1 %view0 %update
        ihave Hfinish := Hfinish $$ %cachedA %cachedD %view2 %view1 %view0 %update
        cases update <;> simp only [KptAD.guarded]
        all_goals first | iintro !> !> | iintro !> | skip
        all_goals
          iunfold KptTranslate.continueWith
          iintro %facts Htranslated
          iapply translated_tail capacity shares rs data root address ppn permission access supported tree p2 p1 a d bound rr _
            canonical path facts image fixed whole gen era cpu N continuation post
            $$ Hcert Houter Hmap Htranslated Hfinish
  · ihave Hfinish := Iris.BI.and_elim_l $$ Hfinish
    ihave Hfinish := Hfinish $$ %data
    iapply (Sv39Address.nativeSpec capacity.machine).noncanonical (outerShares shares) (prepare rs data)
      root (outer rs data root ambient rooted) address access supported (effective rs data access effectiveGiven)
      canonical image fixed whole gen era cpu continuation post $$ Hcert Houter
    iintro Houter
    ihave Hcells := (split_cells capacity era cpu (prepare rs data) shares).mpr $$ [Houter Hinner]
    · iframe Houter Hinner
    ihave ⟨Haux,Hdata⟩ := (partition capacity era cpu rs shares data).mp $$ Hcells
    iunfold continueWith at Hfinish
    isimp only [result] at Hfinish
    iapply Hfinish $$ %canonical [Haux Hdata Hsnapshot Hcredential Hresv]
    iunfold resources
    simp only [afterData, afterReservation, receipts]
    iframe Haux Hmap Hresv
    iunfold opened
    iframe Hdata Hsnapshot Hshared Hcredential
    isplit
    · ipureintro; exact rooted
    · ipureintro; exact tor

theorem actual : Spec capacity := ⟨wp_translate capacity⟩

end Xv6.Kernel.KptAddress
