import Xv6.Kernel.MycpuMemorySpec
import Xv6.Kernel.MycpuMemoryPlan
import MachCSL.Logic.SupervisorWriteProofs
import MachCSL.Logic.SupervisorReadProofs

namespace Xv6.Kernel.MycpuMemory
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions TsoContextReadWP
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
  (capacity : MachineInterp.Capacity GF)

theorem wp_store (slot : Slot) (shares : Shares) (rs : RegisterFile) (region : PMA_Region)
    (config : WriteConfig slot rs region) image fixed whole gen era cpu ξ (old : BitVec 64) rr
    (continuation : ExecutionResult → SailM Unit) post :
iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs slot shares shares.data -∗ running capacity era cpu ξ -∗
      wordPointsto capacity era ξ (address slot rs) (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs slot shares shares.data -∗ running capacity era cpu ξ -∗
        wordPointsto capacity era ξ (address slot rs) (.own 1) (dataValue slot rs) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (storeBody slot >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hresv Hfinish
  ihave %aligned := TsoContextWord.aligned (contextCapacity capacity) (contextNames era)
    ξ (address slot rs) (.own 1) old $$ Hword
  obtain ⟨tail, cut, success, _error⟩ := store_boundary slot shares rs region config aligned
  have gate := SupervisorWrite.Boundary.fold capacity (footprint slot shares shares.data)
    (footprint_unique slot shares shares.data) rs (SupervisorWrite.request (address slot rs) (dataValue slot rs))
    (storeBody slot) tail cut old (dataValue slot rs) rfl
    (SupervisorWrite.request_ram _ _ config.memory.range) (by rfl)
    image fixed whole gen era cpu ξ rr continuation post
  rw [show (SupervisorWrite.request (address slot rs) (dataValue slot rs)).pa = address slot rs from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword Hresv
  iintro !> %view Hregs Hrun Hword Hresv Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hword Hresv Hreceipt

theorem wp_load (slot : Slot) (shares : Shares) (rs : RegisterFile) (region : PMA_Region)
    (config : ReadConfig slot rs region) image fixed whole gen era cpu ξ dq (word : BitVec 64) rr
    (continuation : ExecutionResult → SailM Unit) post :
iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs slot shares (.own 1) -∗ running capacity era cpu ξ -∗
      wordPointsto capacity era ξ (address slot rs) dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu (after slot rs word) slot shares (.own 1) -∗ running capacity era cpu ξ -∗
        wordPointsto capacity era ξ (address slot rs) dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (loadBody slot >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hresv Hfinish
  ihave %aligned := TsoContextWord.aligned (contextCapacity capacity) (contextNames era)
    ξ (address slot rs) dq word $$ Hword
  obtain ⟨tail, cut, success, _error⟩ := load_boundary slot shares rs region config aligned
  have gate := SupervisorRead.Boundary.fold capacity (footprint slot shares (.own 1))
    (footprint_unique slot shares (.own 1)) rs (SupervisorRead.request (address slot rs))
    (loadBody slot) tail cut (SupervisorPhysical.device_ram _ 8 config.memory.range) (by rfl)
    image fixed whole gen era cpu ξ dq word continuation post
  rw [show (SupervisorRead.request (address slot rs)).pa = address slot rs from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  rw [success]
  iapply RegisterPlan.fold capacity (footprint slot shares (.own 1)) (footprint_unique slot shares (.own 1))
    image fixed whole gen era cpu rs (loadTail slot word) _ continuation post
    (load_tail_plan slot shares rs word) $$ Hcert Hregs
  iintro %result %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hfinish $$ %view Hregs Hrun Hword Hresv Hreceipt

theorem actual : Spec capacity := ⟨wp_store capacity, wp_load capacity⟩

end Xv6.Kernel.MycpuMemory
