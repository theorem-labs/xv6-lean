import Xv6.Kernel.MycpuRegimeShellSpec
import Xv6.Kernel.MycpuCycleShellProofs
import Xv6.Kernel.MycpuOffPure

namespace Xv6.Kernel.MycpuRegimeShell
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  have keys : (footprint shares).map Prod.fst = (footprint sourceShares).map Prod.fst := rfl
  unfold RegisterFootprint.Unique
  rw [keys]
  decide

theorem footprint_length (shares : Shares) : (footprint shares).length = 50 := rfl

theorem excludes_translation (shares : Shares) (r : Register)
    (h : r ∈ [.satp, .tlb, .pmpcfg_n, .pmpaddr_n]) : r ∉ (footprint shares).map Prod.fst := by
  have keys : (footprint shares).map Prod.fst = (footprint sourceShares).map Prod.fst := rfl
  rw [keys]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem control_unique (shares : Shares) : RegisterFootprint.Unique (controlFootprint shares) := by
  simp [RegisterFootprint.Unique, controlFootprint, SupervisorRetirement.pcFootprint,
    SupervisorRetirement.retirementFootprint, SupervisorClock.clockFootprint]

theorem setup_frame (control : RegisterFile) (r : Register) (different : r ≠ .minstret_increment) :
    started control r = control r := MycpuCycleShell.started_other control r different

theorem completed_status (control after : RegisterFile) (done : Completed control after) :
    after .mstatus = control .mstatus :=
  MycpuCycleShell.completed_other control after done .mstatus (by decide) (by decide) (by decide)

theorem pureSpec : PureSpec :=
  ⟨footprint_unique, footprint_length, excludes_translation, setup_frame,
    MycpuCycleShell.completed_pc, completed_status⟩

def setupMembers (s : Shares) : SupervisorRetirement.SetupMembers (controlFootprint s) where
  privilege := s.privilege
  inhibit := .discard
  config := .discard
  readPrivilege := by simp [controlFootprint]
  readInhibit := by simp [controlFootprint, SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint]
  readConfig := by simp [controlFootprint, SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint]
  writeFlag := by simp [controlFootprint, SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint]

def completeMembers (s : Shares) : SupervisorRetirement.CompleteMembers (controlFootprint s) where
  hart := s.hart
  next := .own 1
  readHart := by simp [controlFootprint]
  readNext := by simp [controlFootprint, SupervisorRetirement.pcFootprint]
  writePC := by simp [controlFootprint, SupervisorRetirement.pcFootprint]
  writeCounter := by simp [controlFootprint, SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint]
  readFlag := .own 1
  readFlagMember := by simp [controlFootprint, SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint]

theorem clock_member (s : Shares) (r : Register) (member : r ∈ SupervisorClock.clockRegisters) :
    (r, .own 1) ∈ controlFootprint s := by
  simp only [SupervisorClock.clockRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [controlFootprint, SupervisorRetirement.pcFootprint, SupervisorClock.clockFootprint]

theorem start_prefix [Platform] (s : Shares) (control : RegisterFile)
    (enabled : control .hart_state = .HART_ACTIVE ()) (tick : Bool) :
    MycpuActive.Prefix (controlFootprint s) control (cycle tick) (active tick) (started control) := by
  rw [MycpuCycleShell.cycle_factor]
  refine .prefix (SupervisorRetirement.setup_plan _ (setupMembers s) control) ?_
  refine .prefix (value := (started control) .hart_state)
    (.read (dq := s.hart) (by simp [controlFootprint]) (.pure ⟨rfl, rfl⟩)) ?_
  rw [setup_frame _ _ (by decide), enabled]
  exact .done

end Xv6.Kernel.MycpuRegimeShell
