import MachCSL.Machine.SupervisorBareProofs
import MachCSL.Logic.RegisterPlanProofs

namespace MachCSL.Machine.SupervisorBare
open LeanPaperStock.Functions MachCSL.Logic MachCSL.Logic.RegisterPlan Iris
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem returns_bind {fp : RegisterFootprint.Footprint}
    {rs middle after : RegisterFile} {program : SailM α} {next : α → SailM β}
    {value : α} {result : β}
    (first : Returns fp rs program value middle)
    (rest : Returns fp middle (next value) result after) :
    Returns fp rs (program >>= next) result after :=
  Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint)
    (rs : RegisterFile) (value : α) : Returns fp rs (pure value) value rs :=
  .pure ⟨rfl, rfl⟩

private theorem read_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r, dq) ∈ fp) :
    Returns fp rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl, rfl⟩)

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : Returns fp rs program value rs) (ε : Type) :
    Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact returns_bind plan (pure_plan fp rs _)

private theorem except_bind {fp : RegisterFootprint.Footprint} {program : SailME ε α}
    {next : α → SailME ε β} {rs : RegisterFile} {a : α} {b : Except ε β}
    (first : Returns fp rs program.run (.ok a) rs)
    (second : Returns fp rs (next a).run b rs) :
    Returns fp rs (program >>= next).run b rs := returns_bind first second

/-- Actual supervisor architecture queries SXL, not misa. -/
theorem architecture_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (share : DFrac) (member : (.mstatus, share) ∈ fp)
    (sxl : _get_Mstatus_SXL (rs .mstatus) = 2#2) :
    Returns fp rs (architecture .Supervisor) .RV64 rs := by
  unfold architecture
  refine returns_bind (read_plan rs .mstatus share member) ?_
  rw [sxl]
  exact pure_plan fp rs _

/-- Two actual reads: mstatus, then satp. ASID and PPN are unconstrained. -/
theorem mode_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (statusShare satpShare : DFrac)
    (statusMember : (.mstatus, statusShare) ∈ fp)
    (satpMember : (.satp, satpShare) ∈ fp)
    (sxl : _get_Mstatus_SXL (rs .mstatus) = 2#2)
    (bare : _get_Satp64_Mode (Mk_Satp64 (rs .satp)) = 0#4) :
    Returns fp rs (translationMode .Supervisor) .Bare rs := by
  unfold translationMode
  refine returns_bind (architecture_plan rs statusShare statusMember sxl) ?_
  refine returns_bind (middle := rs) (value := 0#4) ?_ ?_
  · refine returns_bind (pure_plan fp rs ()) ?_
    refine returns_bind (read_plan rs .satp satpShare satpMember) ?_
    rw [bare]
    exact pure_plan fp rs _
  · exact pure_plan fp rs _

set_option maxRecDepth 100000 in
theorem translate_plan (shares : Shares) (rs : RegisterFile) (config : Config rs)
    (address : BitVec 64) (access : MemoryAccessType mem_payload)
    (supported : Supported access) (effective : Effective rs access) :
    Returns (footprint shares) rs (translateAddr (.Virtaddr address) access)
      (.Ok (.Physaddr address, .PBMT_PMA, ())) rs := by
  unfold translateAddr _root_.Sail.SailME.run PreSail.PreSailME.run
  refine returns_bind (value := Except.ok (.Ok (.Physaddr address, .PBMT_PMA, ()))) ?_
    (pure_plan (footprint shares) rs _)
  refine except_bind (lift_except (read_plan rs .mstatus shares.status (by simp [footprint])) _) ?_
  refine except_bind (lift_except (read_plan rs .cur_privilege shares.privilege
    (by simp [footprint])) _) ?_
  rw [config.privilege, effective_supervisor rs access effective]
  refine except_bind (lift_except (pure_plan (footprint shares) rs Privilege.Supervisor) _) ?_
  refine except_bind (lift_except (mode_plan rs shares.status shares.satp
    (by simp [footprint]) (by simp [footprint]) config.sxl config.mode) _) ?_
  rw [not_shadow access supported]
  refine except_bind (lift_except (pure_plan (footprint shares) rs false) _) ?_
  refine except_bind (pure_plan (footprint shares) rs _) ?_
  exact pure_plan (footprint shares) rs _

/-- Bare instruction translation needs no MPRV or MPP restriction. -/
theorem fetch_plan (shares : Shares) (rs : RegisterFile) (config : Config rs)
    (address : BitVec 64) :
    Returns (footprint shares) rs (translateAddr (.Virtaddr address) (.InstructionFetch ()))
      (.Ok (.Physaddr address, .PBMT_PMA, ())) rs :=
  translate_plan shares rs config address _ .fetch (Or.inl rfl)

/-- Source MPRV-zero specialization, including arbitrary AMOSWAP aq/rl flags. -/
theorem mprv_zero_plan (shares : Shares) (rs : RegisterFile) (config : Config rs)
    (address : BitVec 64) (access : MemoryAccessType mem_payload) (supported : Supported access)
    (clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1) :
    Returns (footprint shares) rs (translateAddr (.Virtaddr address) access)
      (.Ok (.Physaddr address, .PBMT_PMA, ())) rs :=
  translate_plan shares rs config address access supported (Or.inr clear)

end MachCSL.Machine.SupervisorBare
