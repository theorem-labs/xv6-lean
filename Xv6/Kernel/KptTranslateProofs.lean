import Xv6.Kernel.KptTranslatePureProofs
import Xv6.Kernel.KptHitSpec
import Xv6.Kernel.KptMissSpec
import Xv6.Kernel.KptMissRules

namespace Xv6.Kernel.KptTranslate
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

omit [Platform] in
theorem resources_hit era cpu rs shares asid N root tree bound vpn p2 p1 ppn permission
    cachedA cachedD rr update :
    iprop(⊢ KptHit.resources capacity era cpu rs shares asid N root tree vpn
      (TlbCoherence.entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD))
      (PtTree.addr0 p1 vpn) rr update -∗ clients capacity era cpu N root tree bound -∗
      resources capacity era cpu rs shares N root tree bound asid vpn p2 p1 ppn permission rr
        (.hit cachedA cachedD update)) := by
  iintro Hresources Hclients
  iunfold KptHit.resources at Hresources
  icases Hresources with ⟨Hregs,_,Hresv,Hreceipt,%coherent⟩
  have cellEq : ∀ rs, KptHit.cells capacity era cpu rs shares = cells capacity era cpu rs shares := fun _ => rfl
  isimp only [cellEq] at Hregs
  iunfold resources
  simp only [after, Branch.update, receipts]
  iframe Hregs Hclients Hresv Hreceipt
  ipureintro
  exact coherent

omit [Platform] in
theorem resources_miss era cpu rs shares N root tree bound asid vpn p2 p1 ppn permission
    cachedA cachedD rr view2 view1 view0 update :
    iprop(⊢ KptMiss.resources capacity era cpu rs shares N root tree bound asid vpn p2 p1 ppn
      (KptLeaf.word ppn permission cachedA cachedD) rr view2 view1 view0 update -∗
      resources capacity era cpu rs shares N root tree bound asid vpn p2 p1 ppn permission rr
        (.miss cachedA cachedD view2 view1 view0 update)) := by
  iintro Hresources
  iunfold KptMiss.resources at Hresources
  icases Hresources with ⟨Hregs,Hclients,Hresv,Hwalk,Hreceipt,%coherent⟩
  iunfold resources
  simp only [after, Branch.update, receipts]
  iframe Hregs Hclients Hresv Hwalk Hreceipt
  ipureintro
  exact coherent

variable (hit : KptHit.Spec capacity) (miss : KptMiss.Spec capacity)
include hit miss

/-- The real lookup has already read its owned cell. Coherence and Maps
determinism supply hit residency; empty and rejected entries take the miss. -/
theorem wp_dispatch shares rs asid tree vpn p2 p1 regions (config : Config rs tree vpn p2 p1 regions)
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
        (.hart gen cpu (dispatch asid tree vpn access mxr doSum
          (TlbCoherence.lookupValue (rs .tlb) asid vpn) >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  cases found : TlbCoherence.lookupValue (rs .tlb) asid vpn with
  | none =>
    simp only [dispatch]
    iintro #Hcert Hregs Hclients Hresv Hfinish
    iunfold finish at Hfinish
    isimp only [] at Hfinish
    ihave Hfinish := Iris.BI.and_elim_r $$ Hfinish
    iapply miss.miss shares rs asid tree vpn p2 p1 regions config ppn permission referenceA referenceD
      mapped coherent access supported allowed mxr doSum image fixed whole gen era cpu N root bound rr
      continuation post $$ Hcert Hregs Hclients Hresv
    iunfold KptMiss.finish
    iintro !> !> !> %cachedA %cachedD %view2 %view1 %view0 %update
    ihave Hfinish := Hfinish $$ %cachedA %cachedD %view2 %view1 %view0 %update
    cases update <;> simp only [KptAD.guarded]
    all_goals first | iintro !> !> | iintro !> | skip
    all_goals
      iintro %facts Hresources
      iunfold continueWith at Hfinish
      isimp only [result, Branch.update] at Hfinish
      iapply Hfinish $$ %⟨found,facts⟩ [Hresources]
      iapply resources_miss capacity $$ Hresources
  | some pair =>
    obtain ⟨idx,ent⟩ := pair
    obtain ⟨rfl,resident,cachedA,cachedD,rfl⟩ := lookup_mapped asid tree (rs .tlb) vpn p2 p1
      ppn permission referenceA referenceD idx ent mapped coherent found
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (KptHit.program asid vpn
          (TlbCoherence.entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD))
          access mxr doSum >>= continuation)) post)
    iintro #Hcert Hregs #Hclients Hresv Hfinish
    iunfold finish at Hfinish
    isimp only [] at Hfinish
    ihave Hfinish := Iris.BI.and_elim_l $$ Hfinish
    have cellEq : cells capacity era cpu rs shares = KptHit.cells capacity era cpu rs shares := rfl
    isimp only [cellEq] at Hregs
    ihave Hadclients := KptMiss.clients_ad capacity era cpu N root tree bound $$ Hclients
    iapply hit.hit shares rs asid tree vpn p2 p1 ppn permission referenceA referenceD cachedA cachedD
      (regions 0) config.update mapped coherent resident access supported allowed mxr doSum
      image fixed whole gen era cpu N root rr continuation post $$ Hcert Hregs Hadclients Hresv
    iintro %update
    ihave Hfinish := Hfinish $$ %cachedA %cachedD %update
    cases update <;> simp only [KptAD.guarded]
    all_goals first | iintro !> !> | iintro !> | skip
    all_goals
      iintro %facts Hresources
      iunfold continueWith at Hfinish
      isimp only [result, Branch.update, KptMiss.result] at Hfinish
      isimp only [KptHit.result]
      iapply Hfinish $$ %⟨found,facts⟩ [Hresources]
      iapply resources_hit capacity $$ Hresources Hclients

/-- Native one-read prefix on the same six cells, followed by the complete
shared hit/miss rules. No body WP or state-preservation oracle is input. -/
theorem wp_translate shares rs asid tree vpn p2 p1 regions (config : Config rs tree vpn p2 p1 regions)
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
  have unique : RegisterFootprint.Unique (footprint shares) := by
    simp [RegisterFootprint.Unique, footprint, KptMiss.footprint, KptAD.footprint,
      SupervisorPteAD.footprint, SupervisorPteRead.footprint, SupervisorRead.footprint]
  rw [program_factor, BootPmp.sail_bind_assoc]
  iintro #Hcert Hregs Hclients Hresv Hfinish
  iunfold cells at Hregs
  iunfold KptMiss.cells at Hregs
  iapply RegisterPlan.fold (hlc := hlc) capacity.machine (footprint shares) unique
    image fixed whole gen era cpu rs _
    (fun value afterRs => value = TlbCoherence.lookupValue (rs .tlb) asid vpn ∧ afterRs = rs)
    (fun found => dispatch asid tree vpn access mxr doSum found >>= continuation) post
    (lookup_plan shares rs asid vpn) $$ Hcert Hregs
  iintro %value %afterRs %same Hregs
  rcases same with ⟨valueEq,afterEq⟩
  subst value
  subst afterRs
  have cellEq : RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs
      (footprint shares) = cells capacity era cpu rs shares := rfl
  isimp only [cellEq] at Hregs
  iapply wp_dispatch capacity hit miss shares rs asid tree vpn p2 p1 regions config ppn permission
    referenceA referenceD mapped coherent access supported allowed mxr doSum
    image fixed whole gen era cpu N root bound rr continuation post $$ Hcert Hregs Hclients Hresv Hfinish

theorem actual : Spec capacity := ⟨wp_translate capacity hit miss⟩

end Xv6.Kernel.KptTranslate
