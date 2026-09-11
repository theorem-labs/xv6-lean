import MachCSL.Logic.SupervisorMemOuter4Spec
import MachCSL.Logic.SupervisorMemOuter4Plan
import MachCSL.Logic.SupervisorRead4Link
import MachCSL.Logic.SupervisorWrite4Link

namespace MachCSL.Logic.SupervisorMemOuter4
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_read (shares : Shares) (physical : SupervisorRead4.Shares) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Supervisor) (clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1)
    (address : BitVec 64) (aligned : is_aligned_paddr (.Physaddr address) 4 = true) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 4) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).readable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec 32)
    (continuation : ReadResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ SupervisorRead4.cells capacity era cpu rs physical -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address 4 dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ SupervisorRead4.cells capacity era cpu rs physical -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address 4 dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (readProgram address >>= continuation)) post) := by
  rw [read_factor, BootPmp.sail_bind_assoc]
  iintro #Hcert Hpriv Hphysical Hrun Hword Hcontinue
  iapply RegisterPlan.fold capacity (footprint shares) (SupervisorMemOuter.footprint_unique shares)
    image fixed whole gen era cpu rs (effective (.Load .Data)) _
    (fun result => mem_read_priv (.Load .Data) .PBMT_PMA result (.Physaddr address)
      4 false false false >>= continuation) post
    (SupervisorMemOuter.effective_plan shares rs _ priv (Or.inr clear)) $$ Hcert Hpriv
  iintro %result %file %same Hpriv
  rcases same with ⟨rfl, hfile⟩
  subst file
  rw [read_supervisor, BootPmp.sail_bind_assoc]
  iapply SupervisorRead4.wp_checked_read capacity physical rs address aligned config range disabled region
    matched grant image fixed whole gen era cpu ξ dq word
    (fun result => pure (MemoryOpResult_drop_meta result) >>= continuation) post
    $$ Hcert Hphysical Hrun Hword
  iintro !> %view Hphysical Hrun Hword Hreceipt
  simp only [MemoryOpResult_drop_meta, BootPmp.sail_pure_bind]
  iapply Hcontinue $$ %view Hpriv Hphysical Hrun Hword Hreceipt

theorem wp_write (shares : Shares) (physical : SupervisorWrite4.Shares) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Supervisor) (clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1)
    (address : BitVec 64) (aligned : is_aligned_paddr (.Physaddr address) 4 = true) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 4) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).writable = true)
    image fixed whole gen era cpu ξ (old new : BitVec 32) rr
    (continuation : SupervisorWrite4.Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ SupervisorWrite4.cells capacity era cpu rs physical -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address 4 (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ SupervisorWrite4.cells capacity era cpu rs physical -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address 4 (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (writeProgram address new >>= continuation)) post) := by
  rw [write_factor, BootPmp.sail_bind_assoc]
  iintro #Hcert Hpriv Hphysical Hrun Hword Hresv Hcontinue
  iapply RegisterPlan.fold capacity (footprint shares) (SupervisorMemOuter.footprint_unique shares)
    image fixed whole gen era cpu rs (effective (.Store .Data)) _
    (fun result => mem_write_value_priv_meta (.Physaddr address) 4 new (.Store .Data)
      .PBMT_PMA result () false false false >>= continuation) post
    (SupervisorMemOuter.effective_plan shares rs _ priv (Or.inr clear)) $$ Hcert Hpriv
  iintro %result %file %same Hpriv
  rcases same with ⟨rfl, hfile⟩
  subst file
  rw [write_supervisor]
  iapply SupervisorWrite4.wp_checked_write capacity physical rs address aligned config range disabled region
    matched grant image fixed whole gen era cpu ξ old new rr continuation post
    $$ Hcert Hphysical Hrun Hword Hresv
  iintro !> %view Hphysical Hrun Hword Hresv Hreceipt
  iapply Hcontinue $$ %view Hpriv Hphysical Hrun Hword Hresv Hreceipt

theorem actual : Spec capacity := ⟨wp_read capacity, wp_write capacity⟩

end MachCSL.Logic.SupervisorMemOuter4
