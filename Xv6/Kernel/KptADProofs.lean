import Xv6.Kernel.KptADReadProofs
import Xv6.Kernel.KptADWriteProofs
import Xv6.Kernel.KptADGuardProofs
import Xv6.Kernel.KptLeafLink
import Xv6.Kernel.Sv39WalkPure

namespace Xv6.Kernel.KptAD
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
open SupervisorPteAD (afterRead afterCheck afterWrite afterGate)
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

private theorem fold_leaf (plans : KptLeaf.PlanSpec) (rs : RegisterFile)
    (ppn : BitVec 44) (permission : KptLeaf.Permission) (a d : Bool) vpn address access
    (supported : KptLeaf.Supported access) (allows : KptLeaf.Allows permission access) mxr doSum
    image fixed whole gen era cpu
    (continuation : _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (continuation (.Ok (ppn, .PBMT_PMA, ())))) post -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (KptLeaf.program ppn permission a d vpn address access mxr doSum >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hfinish
  iapply RegisterPlan.fold (hlc := hlc) capacity.machine [] (by simp [RegisterFootprint.Unique]) image fixed whole gen era cpu rs
    (KptLeaf.program ppn permission a d vpn address access mxr doSum)
    (fun value after => value = .Ok (ppn, .PBMT_PMA, ()) ∧ after = rs)
    continuation post (plans.check rs ppn permission a d vpn address access supported allows mxr doSum)
    $$ Hcert []
  · iunfold RegisterFootprint.cells
    itrivial
  iintro %value %after %same _
  rcases same with ⟨rfl, rfl⟩
  iunfold MemoryWriteWP.threadWP at Hfinish
  iunfold RegisterWP.threadWP
  ieval (change _ ⊢ DeadThread.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Ok (ppn, .PBMT_PMA, ())))) post)
  iexact Hfinish


private theorem wp_enabled (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region)
    (N : Namespace) root tree vpn p2 p1 (ppn : BitVec 44) permission (a d : Bool)
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission a d))
    (location : address = PtTree.addr0 p1 vpn) (cached : BitVec 64)
    access (supported : KptLeaf.Supported access) (allows : KptLeaf.Allows permission access) mxr doSum
    (needs : (update_PTE_Bits cached access).isSome = true) (adue : enabled rs = true)
    image fixed whole gen era cpu rr (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tree address cached
        (KptLeaf.word ppn permission a d) rr access continuation post -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (afterGate vpn address access mxr doSum true >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  simp only [afterGate, ↓reduceIte, BootPmp.sail_bind_assoc]
  iintro #Hcert Hregs Hclients Hresv Hfinish
  iunfold finish at Hfinish
  ihave Hcases := enabled_guards _ $$ Hfinish
  iapply wp_read capacity shares rs address region config.read image fixed whole gen era cpu
    N root tree vpn p2 p1 _ mapped location rr
    (fun response => afterRead vpn address access mxr doSum response >>= continuation) post
    $$ Hcert Hregs Hclients Hresv
  iintro !> %view %observed %canonical Hregs Hclients Hresv Hview
  obtain ⟨observedA,observedD,observedEq⟩ := Sv39Walk.leaf_variant ppn permission observed (by
    rw [canonical, KptLeaf.word_canonical, KptLeaf.word_canonical])
  subst observed
  simp only [afterRead, BootPmp.sail_bind_assoc]
  have checked := fold_leaf (hlc := hlc) capacity KptLeaf.nativePlanSpec rs ppn permission observedA observedD
    vpn (.Physaddr address) access supported allows mxr doSum image fixed whole gen era cpu
    (fun response => afterCheck address (KptLeaf.word ppn permission observedA observedD) access response >>= continuation) post
  ieval (change _ ⊢ MemoryWriteWP.threadWP capacity.machine image fixed whole (.hart gen cpu (KptLeaf.program ppn permission observedA observedD vpn (.Physaddr address) access mxr doSum >>= fun (response : _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) => afterCheck address (KptLeaf.word ppn permission observedA observedD) access response >>= continuation)) post)
  iapply checked $$ Hcert
  simp only [afterCheck]
  cases updated : update_PTE_Bits (KptLeaf.word ppn permission observedA observedD) access with
  | none =>
    simp only [BootPmp.sail_pure_bind]
    ihave Hread := and_elim_l $$ Hcases
    ihave Hfinal := Hread $$ %(KptLeaf.word ppn permission observedA observedD) []
    · ipureintro; exact ⟨needs,adue,canonical,updated⟩
    iunfold result at Hfinal
    iapply Hfinal
    iunfold clientResources
    simp only [afterReservation, receipt]
    iframe Hregs Hclients Hresv
    iexists view
    iexact Hview
  | some new =>
    have newCanonical : PteCanonical.canon new = PteCanonical.canon (KptLeaf.word ppn permission a d) := by
      rw [KptLeaf.word_canonical]
      exact SupervisorPteAD.update_canonical ppn permission observedA observedD access new updated
    simp only [BootPmp.sail_bind_assoc]
    ihave Hwritten := and_elim_r $$ Hcases
    ihave Hfinal := Hwritten $$ %(KptLeaf.word ppn permission observedA observedD) %new
    iapply wp_write capacity shares rs address region config.write image fixed whole gen era cpu
      N root tree vpn p2 p1 _ mapped location (KptLeaf.word ppn permission observedA observedD) new newCanonical
      (fun response => afterWrite new () response >>= continuation) post $$ Hcert Hregs Hclients Hresv
    iintro !> %time %positive Hregs Hclients Hmessage Hresv HwrittenView
    simp only [afterWrite, BootPmp.sail_pure_bind]
    iunfold result at Hfinal
    iapply Hfinal $$ []
    · ipureintro; exact ⟨needs,adue,canonical,updated,newCanonical⟩
    iunfold clientResources
    simp only [afterReservation, receipt]
    iframe Hregs Hclients Hresv
    iexists time
    iframe Hmessage HwrittenView
    ipureintro; exact positive

/-- Compose the exact cached/gate/shared-reread/check/shared-write program.
Every result fact is proved from the generated branch actually taken. -/
theorem wp_update (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region)
    (N : Namespace) root tree vpn p2 p1 (ppn : BitVec 44) permission (a d cachedA cachedD : Bool)
    (mapped : PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission a d))
    (location : address = PtTree.addr0 p1 vpn)
    access (supported : KptLeaf.Supported access) (allows : KptLeaf.Allows permission access) mxr doSum
    image fixed whole gen era cpu rr (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tree address
        (KptLeaf.word ppn permission cachedA cachedD) (KptLeaf.word ppn permission a d)
        rr access continuation post -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program vpn address (KptLeaf.word ppn permission cachedA cachedD)
          access mxr doSum >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  unfold program
  rw [SupervisorPteAD.program_eq]
  cases cachedUpdate : update_PTE_Bits (KptLeaf.word ppn permission cachedA cachedD) access with
  | none =>
    simp only [BootPmp.sail_pure_bind]
    iintro #Hcert Hregs Hclients Hresv Hfinish
    iunfold finish at Hfinish
    ihave Hfinal := Hfinish $$ %Branch.cached
    iunfold guarded at Hfinal
    iunfold result at Hfinal
    iapply Hfinal $$ []
    · ipureintro; exact cachedUpdate
    iunfold clientResources
    simp only [afterReservation, receipt]
    iframe Hregs Hclients Hresv
  | some new =>
    have needs : (update_PTE_Bits (KptLeaf.word ppn permission cachedA cachedD) access).isSome = true := by
      rw [cachedUpdate]; rfl
    simp only [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hclients Hresv Hfinish
    iapply RegisterPlan.fold (hlc := hlc) capacity.machine (footprint shares)
      (SupervisorPteAD.footprint_unique shares) image fixed whole gen era cpu rs SupervisorPteAD.gate
      (fun value after => value = enabled rs ∧ after = rs)
      (fun value => afterGate vpn address access mxr doSum value >>= continuation) post
      (SupervisorPteAD.gate_plan shares rs) $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨valueEq, afterEq⟩
    subst after
    subst value
    cases adue : enabled rs with
    | false =>
      simp only [afterGate, Bool.false_eq_true, ↓reduceIte, BootPmp.sail_pure_bind]
      iunfold finish at Hfinish
      ihave Hfinal := Hfinish $$ %Branch.disabled
      iunfold guarded at Hfinal
      iunfold result at Hfinal
      iapply Hfinal $$ []
      · ipureintro; exact ⟨needs,adue⟩
      iunfold clientResources
      simp only [afterReservation, receipt]
      iframe Hregs Hclients Hresv
    | true =>
      iapply wp_enabled capacity shares rs address region config N root tree vpn p2 p1 ppn permission a d
        mapped location (KptLeaf.word ppn permission cachedA cachedD) access supported allows mxr doSum needs adue
        image fixed whole gen era cpu rr continuation post $$ Hcert Hregs Hclients Hresv Hfinish

theorem actual : Spec capacity := ⟨wp_read capacity, wp_write capacity, wp_update capacity⟩

end Xv6.Kernel.KptAD
