import MachCSL.Logic.SupervisorMemOuterSpec
import MachCSL.Logic.SupervisorMemOuterPlan
import MachCSL.Logic.SupervisorReadLink
import MachCSL.Logic.SupervisorWriteLink

namespace MachCSL.Logic.SupervisorMemOuter
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_read (shares : Shares) (physical : SupervisorRead.Shares) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Supervisor) (clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1)
    (kind : SupervisorRead.Kind) (address : BitVec 64) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 8) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (SupervisorRead.access kind))
    image fixed whole gen era cpu ξ dq (word : BitVec 64)
    (continuation : ReadResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ SupervisorRead.cells capacity era cpu rs physical -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ SupervisorRead.cells capacity era cpu rs physical -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (readProgram kind address >>= continuation)) post) := by
  rw [read_factor, BootPmp.sail_bind_assoc]
  iintro #Hcert Hpriv Hphysical Hrun Hword Hcontinue
  iapply RegisterPlan.fold capacity (footprint shares) (footprint_unique shares)
    image fixed whole gen era cpu rs (effective (SupervisorRead.access kind)) _
    (fun result => mem_read_priv (SupervisorRead.access kind) .PBMT_PMA result (.Physaddr address)
      8 false false false >>= continuation) post
    (effective_plan shares rs _ priv (Or.inr clear)) $$ Hcert Hpriv
  iintro %result %file %same Hpriv
  rcases same with ⟨rfl, hfile⟩
  subst file
  rw [read_supervisor, BootPmp.sail_bind_assoc]
  iapply SupervisorRead.wp_checked_read capacity physical rs kind address config range disabled region
    matched grant image fixed whole gen era cpu ξ dq word
    (fun result => pure (MemoryOpResult_drop_meta result) >>= continuation) post
    $$ Hcert Hphysical Hrun Hword
  iintro !> %view Hphysical Hrun Hword Hreceipt
  simp only [MemoryOpResult_drop_meta, BootPmp.sail_pure_bind]
  iapply Hcontinue $$ %view Hpriv Hphysical Hrun Hword Hreceipt

theorem wp_write (shares : Shares) (physical : SupervisorWrite.Shares) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Supervisor) (clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1)
    (address : BitVec 64) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 8) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).writable = true)
    image fixed whole gen era cpu ξ (old new : BitVec 64) rr
    (continuation : SupervisorWrite.Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ SupervisorWrite.cells capacity era cpu rs physical -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ address (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ SupervisorWrite.cells capacity era cpu rs physical -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ address (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (writeProgram address new >>= continuation)) post) := by
  rw [write_factor, BootPmp.sail_bind_assoc]
  iintro #Hcert Hpriv Hphysical Hrun Hword Hresv Hcontinue
  iapply RegisterPlan.fold capacity (footprint shares) (footprint_unique shares)
    image fixed whole gen era cpu rs (effective (.Store .Data)) _
    (fun result => mem_write_value_priv_meta (.Physaddr address) 8 new (.Store .Data)
      .PBMT_PMA result () false false false >>= continuation) post
    (effective_plan shares rs _ priv (Or.inr clear)) $$ Hcert Hpriv
  iintro %result %file %same Hpriv
  rcases same with ⟨rfl, hfile⟩
  subst file
  rw [SupervisorWrite.value_priv_meta_eq]
  iapply SupervisorWrite.wp_checked_write capacity physical rs address config range disabled region
    matched grant image fixed whole gen era cpu ξ old new rr continuation post
    $$ Hcert Hphysical Hrun Hword Hresv
  iintro !> %view Hphysical Hrun Hword Hresv Hreceipt
  iapply Hcontinue $$ %view Hpriv Hphysical Hrun Hword Hresv Hreceipt

theorem actual : Spec capacity := ⟨wp_read capacity, wp_write capacity⟩

end MachCSL.Logic.SupervisorMemOuter
