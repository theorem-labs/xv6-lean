import MachCSL.Logic.SupervisorWriteEA4Spec
import MachCSL.Logic.SupervisorDataPmaLink
import MachCSL.Logic.SupervisorMemOuterPlan
import MachCSL.Logic.SupervisorPmpProofs

namespace MachCSL.Logic.SupervisorWriteEA4
open Iris MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem returns_bind {fp : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact returns_bind plan (pure_plan fp rs _)

private theorem except_bind {fp : RegisterFootprint.Footprint} {program : SailME ε α}
    {next : α → SailME ε β} {rs : RegisterFile} {a : α} {b : Except ε β}
    (first : RegisterPlan.Returns fp rs program.run (.ok a) rs)
    (second : RegisterPlan.Returns fp rs (next a).run b rs) :
    RegisterPlan.Returns fp rs (program >>= next).run b rs := returns_bind first second

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique,SupervisorWriteEA.footprint]

/-- Actual announcement has no V1 write event. The surrounding permission
reads remain part of program_plan. -/
theorem announcement (address : BitVec 64) :
    write_ram_ea .Write_plain (.Physaddr address) 4 = () := rfl

theorem program_plan (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region) :
    RegisterPlan.Returns (footprint shares) rs (program address) (.Ok ()) rs := by
  let fp := footprint shares
  have hpma := SupervisorDataPma.priority_plan rs shares.pma
    (show (.pma_regions, shares.pma) ∈ fp by simp [fp,SupervisorWriteEA.footprint]) .store address 4 region
    config.matched config.writable config.aligned
  have hpmp : RegisterPlan.Returns fp rs
      (pmpCheck (.Physaddr address) 4 (.Store .Data) .Supervisor) none rs := by
    apply widen (Logic.SupervisorPmp.check_ram_plan (shares.cfg, shares.addr) rs config.tor
      address 4 config.range.1 config.range.2.1 config.range.2.2 (.Store .Data) .store)
    intro cell member
    simp only [Logic.SupervisorPmp.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [fp,SupervisorWriteEA.footprint]
  unfold program mem_write_ea _root_.Sail.SailME.run PreSail.PreSailME.run
  refine returns_bind (value := Except.ok (.Ok ())) ?_ (pure_plan fp rs _)
  refine except_bind (lift_except (value := rs .mstatus)
    (RegisterPlan.Plan.read (dq := shares.status) (by simp [SupervisorWriteEA.footprint])
      (.pure ⟨rfl, rfl⟩)) Result) ?_
  refine except_bind (lift_except (value := rs .cur_privilege)
    (RegisterPlan.Plan.read (dq := shares.privilege) (by simp [SupervisorWriteEA.footprint])
      (.pure ⟨rfl, rfl⟩)) Result) ?_
  rw [config.privilege, SupervisorBare.effective_supervisor rs (.Store .Data) (Or.inr config.mprv)]
  refine except_bind (lift_except (pure_plan fp rs Privilege.Supervisor) Result) ?_
  refine except_bind (a := SupervisorPhysical.alignedInfo) ?_ ?_
  · exact returns_bind (lift_except hpma _) (pure_plan fp rs _)
  refine except_bind (a := ((1, 4) : Int × Int)) (pure_plan fp rs _) ?_
  refine except_bind (a := write_kind.Write_plain) (lift_except (pure_plan fp rs _) _) ?_
  refine returns_bind (value := Except.ok (true, (0 : Nat))) ?_ (pure_plan fp rs _)
  simp only [untilFuelM]
  refine returns_bind (value := Except.ok (true, (0 : Nat))) ?_ (pure_plan fp rs _)
  refine except_bind (a := ()) (pure_plan fp rs _) ?_
  dsimp only
  simp only [bits_of_physaddr, Int.toNat, Int.ofNat_zero, Int.zero_mul, SupervisorWrite.add_zero]
  refine returns_bind (lift_except hpmp _) ?_
  exact pure_plan fp rs _

theorem nativePureSpec : PureSpec := ⟨footprint_unique,announcement,program_plan⟩

end MachCSL.Logic.SupervisorWriteEA4
