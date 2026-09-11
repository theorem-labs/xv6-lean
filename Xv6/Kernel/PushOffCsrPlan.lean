import Xv6.Kernel.PushOffCsrSpec
import Xv6.Kernel.MycpuDecodeCertificates
import MachCSL.Logic.SupervisorSstatusOffLink
import MachCSL.Logic.SupervisorWritePlan

namespace Xv6.Kernel.PushOffCsr
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem snapshot_plan (fp : RegisterFootprint.Footprint) (snapshot : JalLoop.Snapshot)
    (rs : RegisterFile) (covered : JalLoop.Covers snapshot rs)
    (members : ∀ r value, snapshot r = some value → ∃ dq, (r, dq) ∈ fp)
    (fuel : Nat) (program : SailM α) (value : α)
    (success : JalLoopPlan.snapshotPlanRun (fun _ _ => none) snapshot fuel program = some value) :
    RegisterPlan.Returns fp rs program value rs := by
  induction fuel generalizing program with
  | zero => simp [JalLoopPlan.snapshotPlanRun] at success
  | succ fuel ih =>
    cases program with
    | pure result =>
      simp only [JalLoopPlan.snapshotPlanRun, Option.some.injEq] at success
      subst result
      exact .pure ⟨rfl, rfl⟩
    | impure event k =>
      cases event <;> simp only [JalLoopPlan.snapshotPlanRun] at success
      all_goals first | contradiction | skip
      case readReg r =>
        split at success
        · cases found : snapshot r with
          | none => simp [found] at success
          | some actual =>
            simp only [found, Option.bind_some] at success
            have rest := ih _ success
            rw [← covered r actual found] at rest
            obtain ⟨dq, member⟩ := members r actual found
            exact .read member rest
        · contradiction
      case readMem n req =>
        split at success <;> contradiction



private theorem returns_bind {fp rs middle after} {program : SailM α} {next : α → SailM β} {value result}
    (first : RegisterPlan.Returns fp rs program value middle)
    (rest : RegisterPlan.Returns fp middle (next value) result after) :
    RegisterPlan.Returns fp rs (program >>= next) result after :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl,rfl⟩ => rest

private theorem read_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r,dq) ∈ fp) :
    RegisterPlan.Returns fp rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl,rfl⟩)

private def checkSnapshot : JalLoop.Snapshot := fun r => match r with
  | .misa => some SupervisorSstatusOff.misaValue
  | _ => none

/-- The actual CSR access check reads only MISA for this concrete CSR and
privilege. Its certificate uses ordinary definitional equality. -/
private theorem check_certificate :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) checkSnapshot 1000
      (check_CSR_result 0x100#12 .Supervisor .CSRReadWrite) = some (.CSR_Check_OK ()) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem check_plan fp rs dq (member : (.misa,dq) ∈ fp)
    (misa : rs .misa = SupervisorSstatusOff.misaValue) :
    RegisterPlan.Returns fp rs (check_CSR_result 0x100#12 .Supervisor .CSRReadWrite)
      (.CSR_Check_OK ()) rs := by
  apply snapshot_plan fp checkSnapshot rs _ _ 1000 _ _ check_certificate
  · intro r value found
    cases r <;> simp only [checkSnapshot, Option.some.injEq] at found
    all_goals first | contradiction | subst value
    exact misa
  · intro r value found
    cases r <;> simp only [checkSnapshot, Option.some.injEq] at found
    all_goals first | contradiction | subst value
    exact ⟨dq,member⟩

private theorem read_factor : read_CSR 0x100#12 = (do
    let ms ← PreSail.readReg .mstatus
    pure (_root_.Sail.BitVec.extractLsb (lower_mstatus ms) 63 0) : SailM (BitVec 64)) := rfl

private theorem write_factor (value : BitVec 64) : write_CSR 0x100#12 value = (do
    let ms ← PreSail.readReg .mstatus
    let next ← legalize_sstatus ms value
    PreSail.writeReg .mstatus next
    let final ← PreSail.readReg .mstatus
    pure (.Ok (_root_.Sail.BitVec.extractLsb (lower_mstatus final) 63 0)) :
      SailM (_root_.Sail.Result (BitVec 64) Unit)) := rfl

private theorem write_self (rs : RegisterFile) (r : Register) :
    MachCSL.Sail.Registers.write rs r (rs r) = rs := by
  funext other
  unfold MachCSL.Sail.Registers.write
  split <;> subst_vars <;> rfl

private theorem read_status_plan fp rs dq (member : (.mstatus,dq) ∈ fp) :
    RegisterPlan.Returns fp rs (read_CSR 0x100#12) (lower_mstatus (rs .mstatus)) rs := by
  rw [read_factor]
  apply RegisterPlan.Plan.read member
  exact .pure ⟨SupervisorWrite.full_word _,rfl⟩

private theorem write_status_plan fp rs dq (member : (.mstatus,.own 1) ∈ fp)
    (misaMember : (.misa,dq) ∈ fp) (misa : rs .misa = SupervisorSstatusOff.misaValue)
    (facts : SupervisorBits.MsFacts (rs .mstatus)) (off : _get_Mstatus_SIE (rs .mstatus) = 0#1) :
    RegisterPlan.Returns fp rs (write_CSR 0x100#12 (SupervisorSstatusOff.writeValue (rs .mstatus)))
      (.Ok (lower_mstatus (rs .mstatus))) rs := by
  rw [write_factor]
  apply RegisterPlan.Plan.read member
  change RegisterPlan.Returns fp rs (SupervisorSstatusOff.program (rs .mstatus) >>= _) _ _
  refine returns_bind (SupervisorSstatusOff.nativeSpec.off_plan fp rs dq misaMember misa
    (rs .mstatus) facts off) ?_
  apply RegisterPlan.Plan.write member
  rw [write_self]
  apply RegisterPlan.Plan.read member
  exact .pure ⟨congrArg _ (SupervisorWrite.full_word _),rfl⟩

/-- Actual CSR body: access check, repeated privilege/MS reads, legalizer,
physical MS write, post-write read, x15 write and success callback. -/
theorem body_plan [Platform] fp rs privShare misaShare
    (privMember : (.cur_privilege,privShare) ∈ fp) (misaMember : (.misa,misaShare) ∈ fp)
    (msMember : (.mstatus,.own 1) ∈ fp) (destMember : (.x15,.own 1) ∈ fp)
    (config : Config rs) (facts : SupervisorBits.MsFacts (rs .mstatus))
    (off : _get_Mstatus_SIE (rs .mstatus) = 0#1) :
    RegisterPlan.Returns fp rs body (.Retire_Success ()) (after rs) := by
  change RegisterPlan.Returns fp rs (doCSR 0x100#12 2#64 (.Regidx 15#5) .CSRRC .CSRReadWrite) _ _
  unfold doCSR
  refine returns_bind (read_plan rs .cur_privilege privShare privMember) ?_
  rw [config.1]
  refine returns_bind (check_plan fp rs misaShare misaMember config.2) ?_
  refine returns_bind (read_plan rs .cur_privilege privShare privMember) ?_
  rw [config.1]
  change RegisterPlan.Returns fp rs (read_CSR 0x100#12 >>= _) _ _
  refine returns_bind (read_status_plan fp rs (.own 1) msMember) ?_
  change RegisterPlan.Returns fp rs (write_CSR 0x100#12 (SupervisorSstatusOff.writeValue (rs .mstatus)) >>= _) _ _
  refine returns_bind (write_status_plan fp rs misaShare msMember misaMember config.2 facts off) ?_
  change RegisterPlan.Returns fp rs (.impure (.writeReg .x15 (lower_mstatus (rs .mstatus))) _) _ _
  exact .write destMember (.pure ⟨rfl,rfl⟩)

end Xv6.Kernel.PushOffCsr
