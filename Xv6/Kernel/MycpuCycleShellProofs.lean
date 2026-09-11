import Xv6.Kernel.MycpuCycleShellSpec
import Xv6.Kernel.MycpuCycleBodyPlan
import Xv6.Kernel.MycpuActiveProofs
import MachCSL.Logic.SupervisorRetirementProofs
import MachCSL.Logic.RestartWPProofs

namespace Xv6.Kernel.MycpuCycleShell
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem bind_pure (program : SailM α) : (program >>= pure) = program := by
  induction program with
  | pure value => rfl
  | impure event k ih =>
    exact congrArg (Sail.ArchSem.FreeM.impure event) (funext ih)

/-- Every waiting and active branch of the actual cycle remains in the factor. -/
theorem cycle_factor [Platform] (tick : Bool) : cycle tick = (do
    SupervisorRetirement.setup
    let state ← _root_.Sail.readReg .hart_state
    match state with
    | .HART_WAITING (reason, bits) => run_hart_waiting 0 reason bits false >>= finish tick
    | .HART_ACTIVE () => run_hart_active 0 >>= finish tick) := by
  simp only [cycle, SupervisorRetirement.try_step_factor, BootPmp.sail_bind_assoc]
  congr 1
  funext returnedUnit
  cases returnedUnit
  congr 1
  funext state
  cases state <;> rfl

theorem started_other (rs : RegisterFile) (r : Register) (different : r ≠ .minstret_increment) :
    started rs r = rs r := SupervisorRetirement.setup_other rs _ r different

theorem start_prefix [Platform] (shares : Shares) (rs : RegisterFile)
    (active : rs .hart_state = .HART_ACTIVE ()) (tick : Bool) :
    MycpuActive.Prefix (footprint shares) rs (cycle tick)
      (run_hart_active 0 >>= finish tick) (started rs) := by
  rw [cycle_factor]
  refine .prefix (SupervisorRetirement.setup_plan (footprint shares) (MycpuCycleBody.setupMembers shares) rs) ?_
  refine MycpuActive.Prefix.prefix (value := (started rs) .hart_state)
    (.read (dq := shares.hart) (by simp [footprint, MycpuCycleBody.footprint]) (.pure ⟨rfl, rfl⟩)) ?_
  rw [started_other _ _ (by decide), active]
  exact .done

theorem completed_pc (rs after : RegisterFile) (same : completed rs after) :
    after .PC = rs .nextPC ∧ after .nextPC = rs .nextPC :=
  SupervisorRetirement.completed_clock_pc rs after same

theorem completed_other (rs after : RegisterFile) (same : completed rs after)
    (r : Register) (notPC : r ≠ .PC) (notCounter : r ≠ .minstret)
    (notClock : r ∉ SupervisorClock.clockRegisters) : after r = rs r :=
  (same r notClock).trans (SupervisorRetirement.complete_other rs r notPC notCounter)

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_start (shares : Shares) (rs : RegisterFile) (active : rs .hart_state = .HART_ACTIVE ())
    tick image fixed whole gen era cpu post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      (cells capacity era cpu (started rs) shares -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (run_hart_active 0 >>= finish tick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post) := by
  have gate := MycpuActive.Prefix.fold capacity (footprint shares) (MycpuCycleBody.footprint_unique shares)
    rs (started rs) (cycle tick) (run_hart_active 0 >>= finish tick) (start_prefix shares rs active tick)
    image fixed whole gen era cpu pure post
  simpa only [bind_pure] using gate

theorem wp_finish (shares : Shares) (rs : RegisterFile) (active : rs .hart_state = .HART_ACTIVE ())
    tick bits image fixed whole gen era cpu (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      (∀ after, ⌜completed rs after⌝ -∗ cells capacity era cpu after shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (finish tick (.Step_Execute (.Retire_Success (), bits)) >>= continuation)) post) :=
  SupervisorRetirement.wp_complete_clock capacity (footprint shares) (MycpuCycleBody.footprint_unique shares)
    (MycpuCycleBody.completeMembers shares) image fixed whole gen era cpu rs active bits
    (MycpuCycleBody.clock_members shares .mcycle (by decide))
    (MycpuCycleBody.clock_members shares .mtime (by decide))
    (MycpuCycleBody.clock_members shares .mip (by decide)) tick continuation post

theorem wp_finish_restart (shares : Shares) (rs : RegisterFile) (active : rs .hart_state = .HART_ACTIVE ())
    tick bits image fixed whole gen era cpu rr post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜completed rs after⌝ -∗ ▷ (∀ nextTick,
        cells capacity era cpu after shares -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post)) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (finish tick (.Step_Execute (.Retire_Success (), bits)))) post) := by
  iintro #Hcert Hregs Hresv Hfinish
  have gate := wp_finish capacity shares rs active tick bits image fixed whole gen era cpu pure post
  simp only [bind_pure] at gate
  iapply gate $$ Hcert Hregs
  iintro %after %same Hregs
  ihave Hnext := Hfinish $$ %after []
  · ipureintro; exact same
  · iapply RestartWP.wp_restart_fragment capacity image fixed whole gen era cpu rr post $$ Hcert Hresv
    iintro !> %nextTick Hresv
    iapply Hnext $$ %nextTick Hregs Hresv

theorem actual : Spec capacity := ⟨wp_start capacity, wp_finish capacity, wp_finish_restart capacity⟩

end Xv6.Kernel.MycpuCycleShell
