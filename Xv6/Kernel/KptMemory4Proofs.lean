import Xv6.Kernel.KptMemory4DataProofs
import Xv6.Kernel.KptAddressLink

namespace Xv6.Kernel.KptMemory4
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

private theorem fold {fp : RegisterFootprint.Footprint} (unique : RegisterFootprint.Unique fp)
    {rs : RegisterFile} {body : SailM α} {program : SailM β} {tail : α → SailM β}
    (cut : Sv39Address.Boundary fp rs body program tail)
    image fixed whole gen era cpu (continuation : β → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (body >>= fun result => tail result >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | body =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hfinish
    iapply Hfinish $$ Hregs
  | «prefix» before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hfinish
    iapply RegisterPlan.fold capacity.machine fp unique image fixed whole gen era cpu rs _
      (fun value after => value = _ ∧ after = rs) _ post before $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply ih $$ Hcert Hregs Hfinish

omit [Platform] in
/-- Reassemble precisely the same named source residue after an ordinary
physical data event. The event does not write any of the nine control cells. -/
private theorem close_data shares rs data era cpu N root
    (rooted : KptResidue.SatpRooted root data.satp)
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (KptAddress.prepare rs data)) :
    iprop(⊢ KptAddress.cells capacity era cpu (KptAddress.prepare rs data) shares -∗
      KptResidue.tlbSnapOK capacity era data.tlb -∗ KptShared.shared capacity era N root -∗
      KptShared.credentials capacity era cpu -∗
      auxiliaryCells capacity era cpu rs shares ∗ KptResidue.residue capacity era cpu N root) := by
  iintro Hcells Hsnapshot Hshared Hcredential
  ihave ⟨Haux,Hdata⟩ := (KptAddress.partition capacity era cpu rs shares data).mp $$ Hcells
  iframe Haux
  iapply KptAddress.close_residue capacity era cpu rs N root data
  iunfold KptAddress.opened
  iframe Hdata Hsnapshot Hshared Hcredential
  isplit
  · ipureintro; exact rooted
  · ipureintro; exact tor

theorem completed_tail shares rs data root (ambient : Ambient rs) kind tier ξ va ppn dq old new rr outcome
    (full : kind = .store → dq = .own 1) (positive : KernelDatum.Positive va)
    (aligned : KernelDatumWord4.Aligned (KernelDatum.physical ppn va))
    (ram : KernelDatum.Ram (KernelDatum.physical ppn va))
    (facts : KptAddress.OutcomeFacts rs data root va ppn .rw (access kind) outcome)
    image fixed whole gen era cpu N (continuation : Result kind → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      KptAddress.resources capacity era cpu rs shares N root data va ppn .rw rr outcome -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatumWord4.physicalWord capacity era ξ (KernelDatum.physical ppn va) dq old -∗
      (∀ value, KernelDatumWord4.physicalWord capacity era ξ (KernelDatum.physical ppn va) dq value -∗
        KernelDatumWord4.word capacity era tier ξ va dq value) -∗
      continueWith capacity image fixed whole gen era cpu rs shares N root kind tier ξ va dq old new rr
        continuation post ppn data outcome -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (afterAddress kind va new (KptAddress.result va ppn (access kind) outcome) >>= continuation)) post) := by
  iintro #Hcert Htranslated Hrun Hword Hclose Hfinish
  have done := completed rs data root kind va ppn outcome ambient positive facts
  rw [done.2]
  iunfold continueWith at Hfinish
  ihave Hfinish := Hfinish $$ %done
  iunfold KptAddress.resources at Htranslated
  icases Htranslated with ⟨Haux,Hopened,Hmap,Hresv,Hreceipts⟩
  iunfold KptAddress.opened at Hopened
  icases Hopened with ⟨Hdata,%rooted,Hsnapshot,%tor,Hshared,Hcredential⟩
  ihave Hcells := (KptAddress.partition capacity era cpu rs shares _).mpr $$ [Haux Hdata]
  · iframe Haux Hdata
  cases kind with
  | load =>
    simp only [afterAddress]
    isimp only [result] at Hfinish
    iapply wp_data_read capacity shares rs _ ambient va _ tor aligned ram
      image fixed whole gen era cpu ξ dq old continuation post $$ Hcert Hcells Hrun Hword
    iintro !> %view Hcells Hrun Hword Hview
    ihave Hword := Hclose $$ %old Hword
    ihave ⟨Haux,Hresidue⟩ := close_data capacity shares rs _ era cpu N root rooted tor
      $$ Hcells Hsnapshot Hshared Hcredential
    iapply Hfinish $$ %view [Haux Hresidue Hrun Hword Hresv Hreceipts Hview]
    iunfold resources
    simp only [valueAfter, afterReservation]
    iframe Haux Hresidue Hrun Hword Hresv Hreceipts Hview
  | store =>
    simp only [afterAddress]
    isimp only [result] at Hfinish
    have fraction := full rfl
    subst dq
    iapply wp_data_write capacity shares rs _ ambient va _ new tor aligned ram
      image fixed whole gen era cpu ξ old _ continuation post $$ Hcert Hcells Hrun Hword Hresv
    iintro !> %view Hcells Hrun Hword Hresv Hview
    ihave Hword := Hclose $$ %new Hword
    ihave ⟨Haux,Hresidue⟩ := close_data capacity shares rs _ era cpu N root rooted tor
      $$ Hcells Hsnapshot Hshared Hcredential
    iapply Hfinish $$ %view [Haux Hresidue Hrun Hword Hresv Hreceipts Hview]
    iunfold resources
    simp only [valueAfter, afterReservation]
    iframe Haux Hresidue Hrun Hword Hresv Hreceipts Hview

theorem translate_data shares rs (ambient : Ambient rs) kind tier ξ va ppn dq old new rr
    (full : kind = .store → dq = .own 1) (positive : KernelDatum.Positive va)
    (aligned : KernelDatumWord4.Aligned (KernelDatum.physical ppn va))
    (ram : KernelDatum.Ram (KernelDatum.physical ppn va))
    image fixed whole gen era cpu N root (continuation : Result kind → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      auxiliaryCells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      KptShared.mapAt capacity era (Sv39Address.vpn va) ppn .rw -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatumWord4.physicalWord capacity era ξ (KernelDatum.physical ppn va) dq old -∗
      (∀ value, KernelDatumWord4.physicalWord capacity era ξ (KernelDatum.physical ppn va) dq value -∗
        KernelDatumWord4.word capacity era tier ξ va dq value) -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root kind tier ξ va dq old new rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (KptAddress.program va (access kind) >>= fun response =>
          afterAddress kind va new response >>= continuation)) post) := by
  iintro #Hcert Haux Hresidue #Hmap Hrun Hword Hclose Hresv Hfinish
  have supported : KptLeaf.Supported (access kind) := by cases kind <;> constructor
  have allowed : KptLeaf.Allows .rw (access kind) := by cases kind <;> trivial
  iapply (KptAddress.nativeSpec capacity).translate shares rs ambient.address va ppn .rw (access kind)
    supported allowed (Or.inr ambient.mprv) image fixed whole gen era cpu N root rr
    (fun response => afterAddress kind va new response >>= continuation) post
    $$ Hcert Haux Hresidue Hmap Hresv
  iunfold KptAddress.finish
  isimp only []
  isplit
  · iintro %data
    iunfold KptAddress.continueWith
    iintro %facts Hresources
    exact False.elim (facts (KernelDatum.canonical va positive))
  · iintro %data %tree %p2 %p1 %referenceA %referenceD %_path
    iunfold finish at Hfinish
    isimp only [] at Hfinish
    ihave Hfinish := Hfinish $$ %ppn %data %tree %p2 %p1 %referenceA %referenceD
    isplit
    · ihave Hfinish := Iris.BI.and_elim_l $$ Hfinish
      iintro %a %d %update
      ihave Hfinish := Hfinish $$ %a %d %update
      cases update <;> simp only [KptAD.guarded]
      all_goals first | iintro !> !> | iintro !> | skip
      all_goals
        iunfold KptAddress.continueWith
        iintro %facts Hresources
        iapply completed_tail capacity shares rs data root ambient kind tier ξ va ppn dq old new rr _
          full positive aligned ram facts image fixed whole gen era cpu N continuation post
          $$ Hcert Hresources Hrun Hword Hclose Hfinish
    · ihave Hfinish := Iris.BI.and_elim_r $$ Hfinish
      iintro !> !> !> %a %d %view2 %view1 %view0 %update
      ihave Hfinish := Hfinish $$ %a %d %view2 %view1 %view0 %update
      cases update <;> simp only [KptAD.guarded]
      all_goals first | iintro !> !> | iintro !> | skip
      all_goals
        iunfold KptAddress.continueWith
        iintro %facts Hresources
        iapply completed_tail capacity shares rs data root ambient kind tier ξ va ppn dq old new rr _
          full positive aligned ram facts image fixed whole gen era cpu N continuation post
          $$ Hcert Hresources Hrun Hword Hclose Hfinish

theorem wp_address shares rs (ambient : Ambient rs) kind tier ξ va dq old new rr
    (full : kind = .store → dq = .own 1)
    image fixed whole gen era cpu (N : Namespace) root
    (continuation : Result kind → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      auxiliaryCells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ KernelDatumWord4.word capacity era tier ξ va dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root kind tier ξ va dq old new rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (addressProgram kind va new >>= continuation)) post) := by
  iintro #Hcert Haux Hresidue Hrun Hword Hresv Hfinish
  ihave %aligned := word_aligned capacity era tier ξ va dq old $$ Hword
  ihave ⟨%ppn,Hclaims,Hword,Hclose⟩ := (KernelDatumWord4.nativeSpec capacity).access era tier ξ va dq old $$ Hword
  ihave Hclaim := (KernelDatumWord4.nativeSpec capacity).head era tier va ppn $$ Hclaims
  iunfold KernelDatum.claim at Hclaim
  icases Hclaim with ⟨#Hmap,%facts⟩
  obtain ⟨positive,ram,_pin⟩ := facts
  have alignedPhysical := KernelDatumWord4.physical_aligned va ppn aligned
  ihave ⟨%data,Hopened⟩ := KptAddress.open_residue capacity era cpu rs N root $$ Hresidue
  iunfold KptAddress.opened at Hopened
  icases Hopened with ⟨Hdata,%rooted,Hsnapshot,%tor,Hshared,Hcredential⟩
  ihave Hcells := (KptAddress.partition capacity era cpu rs shares data).mpr $$ [Haux Hdata]
  · iframe Haux Hdata
  isimp only [KptAddress.cells] at Hcells
  iapply fold capacity (KptAddress.unique shares)
    (address shares rs data root ambient rooted va new kind aligned)
    image fixed whole gen era cpu continuation post $$ Hcert Hcells
  iintro Hcells
  ihave Hnamed : KptAddress.cells capacity era cpu (KptAddress.prepare rs data) shares $$ [Hcells]
  · unfold KptAddress.cells
    iexact Hcells
  ihave ⟨Haux,Hresidue⟩ := close_data capacity shares rs data era cpu N root rooted tor
    $$ Hnamed Hsnapshot Hshared Hcredential
  ihave Hmapped : KptShared.mapAt capacity era (Sv39Address.vpn va) ppn .rw $$ [Hmap]
  · unfold KptShared.mapAt Sv39Address.vpn
    isimp only [KernelDatum.vpn] at Hmap
    iexact Hmap
  iapply translate_data capacity shares rs ambient kind tier ξ va ppn dq old new rr full positive
    alignedPhysical ram image fixed whole gen era cpu N root continuation post
    $$ Hcert Haux Hresidue Hmapped Hrun Hword Hclose Hresv Hfinish

theorem wp_transformed shares rs (ambient : Ambient rs) kind tier ξ va dq old new rr
    (full : kind = .store → dq = .own 1)
    image fixed whole gen era cpu (N : Namespace) root
    (continuation : Result kind → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      auxiliaryCells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ KernelDatumWord4.word capacity era tier ξ va dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root kind tier ξ va dq old new rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program kind va new >>= continuation)) post) := by
  iintro #Hcert Haux Hresidue Hrun Hword Hresv Hfinish
  ihave ⟨%data,Hopened⟩ := KptAddress.open_residue capacity era cpu rs N root $$ Hresidue
  iunfold KptAddress.opened at Hopened
  icases Hopened with ⟨Hdata,%rooted,Hsnapshot,%tor,Hshared,Hcredential⟩
  ihave Hcells := (KptAddress.partition capacity era cpu rs shares data).mpr $$ [Haux Hdata]
  · iframe Haux Hdata
  isimp only [KptAddress.cells] at Hcells
  rw [program_factor, BootPmp.sail_bind_assoc]
  all_goals
    iapply RegisterPlan.fold capacity.machine (KptAddress.footprint shares) (KptAddress.unique shares)
      image fixed whole gen era cpu (KptAddress.prepare rs data) _
      (fun value after => value = .Virtaddr va ∧ after = KptAddress.prepare rs data) _ post
      (transform shares rs data root ambient rooted va _) $$ Hcert Hcells
    iintro %value %after %same Hcells
    rcases same with ⟨rfl,rfl⟩
    ihave Hnamed : KptAddress.cells capacity era cpu (KptAddress.prepare rs data) shares $$ [Hcells]
    · unfold KptAddress.cells
      iexact Hcells
    ihave ⟨Haux,Hresidue⟩ := close_data capacity shares rs data era cpu N root rooted tor
      $$ Hnamed Hsnapshot Hshared Hcredential
    ieval (change _ ⊢ MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (addressProgram kind va new >>= continuation)) post)
    iapply wp_address capacity shares rs ambient _ tier ξ va dq old new rr full
      image fixed whole gen era cpu N root continuation post
      $$ Hcert Haux Hresidue Hrun Hword Hresv Hfinish

theorem actual : Spec capacity := ⟨wp_address capacity, wp_transformed capacity⟩

end Xv6.Kernel.KptMemory4
