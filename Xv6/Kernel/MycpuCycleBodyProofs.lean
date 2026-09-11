import Xv6.Kernel.MycpuCycleBodySpec
import Xv6.Kernel.MycpuCycleBodyPlan
import MachCSL.Logic.SupervisorWriteProofs
import MachCSL.Logic.SupervisorReadProofs

namespace Xv6.Kernel.MycpuCycleBody
open MycpuMemory
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions TsoContextReadWP
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
  (capacity : MachineInterp.Capacity GF)

theorem wp_store (slot : Slot) (shares : Shares) (rs : RegisterFile) (region : PMA_Region)
    (config : WriteConfig slot rs region) image fixed whole gen era cpu ξ (old : BitVec 64) rr
    (continuation : ExecutionResult → SailM Unit) post :
iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗
      wordPointsto capacity era ξ (address slot rs) (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗
        wordPointsto capacity era ξ (address slot rs) (.own 1) (dataValue slot rs) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (storeBody slot >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hresv Hfinish
  ihave %aligned := TsoContextWord.aligned (contextCapacity capacity) (contextNames era)
    ξ (address slot rs) (.own 1) old $$ Hword
  obtain ⟨tail, cut, success, _error⟩ := store_boundary shares slot rs region config aligned
  have gate := SupervisorWrite.Boundary.fold capacity (footprint shares)
    (footprint_unique shares) rs (SupervisorWrite.request (address slot rs) (dataValue slot rs))
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
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗
      wordPointsto capacity era ξ (address slot rs) dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu (after slot rs word) shares -∗ running capacity era cpu ξ -∗
        wordPointsto capacity era ξ (address slot rs) dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (loadBody slot >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hresv Hfinish
  ihave %aligned := TsoContextWord.aligned (contextCapacity capacity) (contextNames era)
    ξ (address slot rs) dq word $$ Hword
  obtain ⟨tail, cut, success, _error⟩ := load_boundary shares slot rs region config aligned
  have gate := SupervisorRead.Boundary.fold capacity (footprint shares)
    (footprint_unique shares) rs (SupervisorRead.request (address slot rs))
    (loadBody slot) tail cut (SupervisorPhysical.device_ram _ 8 config.memory.range) (by rfl)
    image fixed whole gen era cpu ξ dq word continuation post
  rw [show (SupervisorRead.request (address slot rs)).pa = address slot rs from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  rw [success]
  iapply RegisterPlan.fold capacity (footprint shares) (footprint_unique shares)
    image fixed whole gen era cpu rs (loadTail slot word) _ continuation post
    (load_tail_plan shares slot rs word) $$ Hcert Hregs
  iintro %result %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hfinish $$ %view Hregs Hrun Hword Hresv Hreceipt



theorem wp_scalar (shares : Shares) (i : Fin 9) image fixed whole gen era cpu rs
    (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      (cells capacity era cpu (MycpuScalar.after i rs) shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (MycpuScalar.body i >>= continuation)) post) := by
  iintro Hcert Hregs Hfinish
  iapply RegisterPlan.fold capacity (footprint shares) (footprint_unique shares)
    image fixed whole gen era cpu rs (MycpuScalar.body i) _ continuation post
    (scalar_plan shares i rs) $$ Hcert Hregs
  iintro %value %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hfinish $$ Hregs

theorem wp_return (shares : Shares) (rs : RegisterFile) (config : MycpuReturn.Config rs)
    image fixed whole gen era cpu (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      (cells capacity era cpu (MycpuReturn.after rs) shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (MycpuReturn.body >>= continuation)) post) := by
  iintro Hcert Hregs Hfinish
  iapply RegisterPlan.fold capacity (footprint shares) (footprint_unique shares)
    image fixed whole gen era cpu rs MycpuReturn.body _ continuation post
    (return_plan shares rs config) $$ Hcert Hregs
  iintro %value %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hfinish $$ Hregs

theorem actual : Spec capacity := ⟨wp_store capacity, wp_load capacity, wp_scalar capacity, wp_return capacity⟩

end Xv6.Kernel.MycpuCycleBody
