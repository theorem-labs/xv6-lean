import Xv6.Kernel.KptMemoryDataPlan
import Xv6.Kernel.KernelDatumWordLink

namespace Xv6.Kernel.KptMemory
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

omit [Platform] in
theorem word_aligned era tier ξ va dq word :
    iprop(KernelDatum.word capacity era tier ξ va dq word ⊢ ⌜TsoContextWord.Aligned va⌝) := by
  iintro Hword
  iunfold KernelDatum.word at Hword
  icases Hword with ⟨%aligned,_⟩
  ipureintro; exact aligned

theorem wp_data_read shares rs data (ambient : Ambient rs) va pa
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (KptAddress.prepare rs data))
    (aligned : TsoContextWord.Aligned pa) (ram : KernelDatum.Ram pa)
    image fixed whole gen era cpu ξ dq old
    (continuation : Result .load → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      KptAddress.cells capacity era cpu (KptAddress.prepare rs data) shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ pa dq old -∗
      ▷ (∀ view, KptAddress.cells capacity era cpu (KptAddress.prepare rs data) shares -∗
        TsoContextReadWP.running capacity.machine era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity.machine era ξ pa dq old -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok old))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (readAfterAddress va (.Ok (.Physaddr pa,.PBMT_PMA,())) >>= continuation)) post) := by
  iintro #Hcert Hcells Hrun Hword Hfinish
  obtain ⟨tail,cut,success,_⟩ := data_read shares rs data ambient va pa tor aligned ram
  have gate := SupervisorRead.Boundary.fold capacity.machine (KptAddress.footprint shares)
    (KptAddress.unique shares) (KptAddress.prepare rs data) (SupervisorRead.request pa)
    _ tail cut (SupervisorPhysical.device_ram pa 8 (data_range pa aligned ram)) (by rfl)
    image fixed whole gen era cpu ξ dq old continuation post
  rw [show (SupervisorRead.request pa).pa = pa from rfl] at gate
  isimp only [KptAddress.cells] at Hcells Hfinish
  iapply gate $$ Hcert Hcells Hrun Hword
  iintro !> %view Hcells Hrun Hword Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hcells Hrun Hword Hreceipt

theorem wp_data_write shares rs data (ambient : Ambient rs) va pa new
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (KptAddress.prepare rs data))
    (aligned : TsoContextWord.Aligned pa) (ram : KernelDatum.Ram pa)
    image fixed whole gen era cpu ξ old rr
    (continuation : Result .store → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      KptAddress.cells capacity era cpu (KptAddress.prepare rs data) shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ pa (.own 1) old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, KptAddress.cells capacity era cpu (KptAddress.prepare rs data) shares -∗
        TsoContextReadWP.running capacity.machine era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity.machine era ξ pa (.own 1) new -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (writeAfterAddress va new (.Ok (.Physaddr pa,.PBMT_PMA,())) >>= continuation)) post) := by
  iintro #Hcert Hcells Hrun Hword Hresv Hfinish
  obtain ⟨tail,cut,success,_⟩ := data_write shares rs data ambient va pa new tor aligned ram
  have gate := SupervisorWrite.Boundary.fold capacity.machine (KptAddress.footprint shares)
    (KptAddress.unique shares) (KptAddress.prepare rs data) (SupervisorWrite.request pa new)
    _ tail cut old new rfl (SupervisorPhysical.device_ram pa 8 (data_range pa aligned ram)) (by rfl)
    image fixed whole gen era cpu ξ rr continuation post
  rw [show (SupervisorWrite.request pa new).pa = pa from rfl] at gate
  isimp only [KptAddress.cells] at Hcells Hfinish
  iapply gate $$ Hcert Hcells Hrun Hword Hresv
  iintro !> %view Hcells Hrun Hword Hresv Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hcells Hrun Hword Hresv Hreceipt

end Xv6.Kernel.KptMemory
