import Xv6.Kernel.PushOffWord4BareReadPlan
import Xv6.Kernel.PushOffWord4BareWritePlan
import Xv6.Kernel.KptMemory4DataProofs

namespace Xv6.Kernel.PushOffWord4Bare
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_address s rs (config : Config rs) kind ξ va dq old new rr
    (aligned : KernelDatumWord4.Aligned va) (range : SupervisorPhysical.RamRange va 4)
    (full : kind = .store → dq = .own 1) image fixed whole gen era cpu
    (continuation : Result kind → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs s -∗ TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ va 4 dq old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs s kind ξ va dq old new rr continuation post -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (addressProgram kind va new >>= continuation)) post) := by
  cases kind with
  | load =>
    iintro #Hcert Hcells Hrun Hword Hresv Hfinish
    iunfold finish at Hfinish
    obtain ⟨tail,cut,success,_⟩ := Read.program_boundary s rs va config range aligned
    have gate := SupervisorFetchRead.Boundary.fold capacity (footprint s) (unique s)
      rs 4 (SupervisorFetchRead.request va 4) _ tail cut (SupervisorPhysical.device_ram va 4 range) (by rfl)
      image fixed whole gen era cpu ξ dq old continuation post
    rw [show (SupervisorFetchRead.request va 4).pa = va from rfl] at gate
    ieval (change _ ⊢ RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (addressProgram .load va 0#32 >>= continuation)) post)
    iapply gate $$ Hcert Hcells Hrun Hword
    iintro !> %view Hcells Hrun Hword Hview
    rw [success, BootPmp.sail_pure_bind]
    isimp only [KptMemory4.result] at Hfinish
    iapply Hfinish $$ %view
    unfold resources afterReservation KptMemory4.valueAfter
    iframe
  | store =>
    have hfull := full rfl
    subst dq
    iintro #Hcert Hcells Hrun Hword Hresv Hfinish
    iunfold finish at Hfinish
    obtain ⟨tail,cut,success,_⟩ := Write.virtual_boundary s rs va new config range aligned
    have gate := SupervisorWrite4.Boundary.fold capacity (footprint s) (unique s)
      rs (SupervisorWrite4.request va new) _ tail cut old new rfl
      (SupervisorPhysical.device_ram va 4 range) (by rfl)
      image fixed whole gen era cpu ξ rr continuation post
    rw [show (SupervisorWrite4.request va new).pa = va from rfl] at gate
    iapply gate $$ Hcert Hcells Hrun Hword Hresv
    iintro !> %view Hcells Hrun Hword Hresv Hview
    rw [success, BootPmp.sail_pure_bind]
    isimp only [KptMemory4.result] at Hfinish
    iapply Hfinish $$ %view
    unfold resources afterReservation KptMemory4.valueAfter
    iframe

theorem wp_transformed s rs (config : Config rs) kind ξ va dq old new rr
    (aligned : KernelDatumWord4.Aligned va) (range : SupervisorPhysical.RamRange va 4)
    (full : kind = .store → dq = .own 1) image fixed whole gen era cpu
    (continuation : Result kind → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs s -∗ TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ va 4 dq old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs s kind ξ va dq old new rr continuation post -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (program kind va new >>= continuation)) post) := by
  iintro #Hcert Hcells Hrun Hword Hresv Hfinish
  unfold program
  rw [KptMemory4.program_factor, BootPmp.sail_bind_assoc]
  iapply RegisterPlan.fold capacity (footprint s) (unique s)
    image fixed whole gen era cpu rs _
    (fun value after => value = .Virtaddr va ∧ after = rs) _ post
    (transform s rs config va kind) $$ Hcert Hcells
  iintro %value %after %same Hcells
  rcases same with ⟨rfl,hafter⟩
  subst after
  ieval (change _ ⊢ RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (addressProgram kind va new >>= continuation)) post)
  iapply wp_address capacity s rs config kind ξ va dq old new rr aligned range full
    image fixed whole gen era cpu continuation post $$ Hcert Hcells Hrun Hword Hresv Hfinish
end Xv6.Kernel.PushOffWord4Bare
