import Xv6.Kernel.MycpuRegimeShellResources
import MachCSL.Logic.SupervisorRetirementProofs
import MachCSL.Logic.RestartWPProofs

namespace Xv6.Kernel.MycpuRegimeShell
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

private theorem bind_pure (program : SailM α) : (program >>= pure) = program := by
  induction program with
  | pure value => rfl
  | impure event k ih => exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_start shares control values regime (enabled : control .hart_state = .HART_ACTIVE ())
    tick image fixed whole gen era cpu (frame : IProp GF) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu regime control values shares -∗ frame -∗
      (resources capacity era cpu regime (started control) values shares -∗ frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (active tick)) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro #Hcert Hresources Hframe Hfinish
  isimp [resources] at Hresources
  icases Hresources with ⟨Hcontrols, Hms, Hoff, Hgpr, Htr⟩
  have gate := MycpuActive.Prefix.fold capacity.machine (controlFootprint shares) (control_unique shares)
    control (started control) (cycle tick) (active tick) (start_prefix shares control enabled tick)
    image fixed whole gen era cpu pure post
  simp only [bind_pure] at gate
  isimp [controls] at Hcontrols
  iapply gate $$ Hcert Hcontrols
  iintro Hcontrols
  iapply Hfinish $$ [Hcontrols Hms Hoff Hgpr Htr] Hframe
  isimp [resources, controls]
  have ms : started control .mstatus = control .mstatus := setup_frame _ _ (by decide)
  isimp [ms]
  iframe

theorem wp_finish shares control values regime (enabled : control .hart_state = .HART_ACTIVE ())
    tick bits image fixed whole gen era cpu (frame : IProp GF)
    (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu regime control values shares -∗ frame -∗
      (∀ after, ⌜Completed control after⌝ -∗
        resources capacity era cpu regime after values shares -∗ frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (MycpuRegimeShell.finish tick (.Step_Execute (.Retire_Success (), bits)) >>= continuation)) post) := by
  iintro #Hcert Hresources Hframe Hfinish
  isimp [resources] at Hresources
  icases Hresources with ⟨Hcontrols, Hms, Hoff, Hgpr, Htr⟩
  isimp [controls] at Hcontrols
  isimp [finish, MycpuCycleShell.finish]
  iapply SupervisorRetirement.wp_complete_clock capacity.machine (controlFootprint shares) (control_unique shares)
    (completeMembers shares) image fixed whole gen era cpu control enabled bits
    (clock_member shares .mcycle (by decide)) (clock_member shares .mtime (by decide))
    (clock_member shares .mip (by decide)) tick continuation post $$ Hcert Hcontrols
  iintro %after %done Hcontrols
  iapply Hfinish $$ %after [] [Hcontrols Hms Hoff Hgpr Htr] Hframe
  · ipureintro; exact done
  · isimp [resources, controls]
    have ms : after .mstatus = control .mstatus := completed_status control after done
    isimp [ms]
    iframe

theorem wp_restart shares control values regime (enabled : control .hart_state = .HART_ACTIVE ())
    tick bits image fixed whole gen era cpu rr (frame : IProp GF) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu regime control values shares -∗ frame -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜Completed control after⌝ -∗ ▷ (∀ nextTick,
        resources capacity era cpu regime after values shares -∗ frame -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (MycpuRegimeShell.finish tick (.Step_Execute (.Retire_Success (), bits)))) post) := by
  iintro #Hcert Hresources Hframe Hresv Hfinish
  have gate := wp_finish capacity shares control values regime enabled tick bits
    image fixed whole gen era cpu frame pure post
  simp only [bind_pure] at gate
  iapply gate $$ Hcert Hresources Hframe
  iintro %after %done Hresources Hframe
  ihave Hnext := Hfinish $$ %after []
  · ipureintro; exact done
  · iapply RestartWP.wp_restart_fragment capacity.machine image fixed whole gen era cpu rr post $$ Hcert Hresv
    iintro !> %nextTick Hresv
    iapply Hnext $$ %nextTick Hresources Hframe Hresv

theorem actual (bits : SupervisorBits.Spec capacity.supervisorBits) : Spec capacity :=
  ⟨partition capacity, disabled capacity bits, wp_start capacity, wp_finish capacity, wp_restart capacity⟩

end Xv6.Kernel.MycpuRegimeShell
