import Xv6.Kernel.MycpuKptCycleSpec
import Xv6.Kernel.MycpuActivePlan
import Xv6.Kernel.MycpuRegimeShellPlan
import Xv6.Kernel.MycpuKptFetchPureProofs

namespace Xv6.Kernel.MycpuKptCycle
open Iris MachCSL.Memory MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
open MycpuActive
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem returns_bind {fp rs middle after} {program : SailM α} {next : α → SailM β} {value result}
    (first : RegisterPlan.Returns fp rs program value middle)
    (rest : RegisterPlan.Returns fp middle (next value) result after) :
    RegisterPlan.Returns fp rs (program >>= next) result after :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem read_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r, dq) ∈ fp) :
    RegisterPlan.Returns fp rs (PreSail.readReg r) (rs r) rs := .read member (.pure ⟨rfl, rfl⟩)

private theorem widen_plan {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

/-- Transfer the existing register-only decoder certificate to a finite owned
footprint. A missing snapshot value, any memory event or write is rejected. -/
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
      exact pure_plan fp rs value
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

theorem decode_plan (shares : Shares) (rs : RegisterFile) (i : Fin 14) (config : MycpuDecode.Config i rs) :
    RegisterPlan.Returns (footprint shares) rs (MycpuDecode.decode i) (MycpuDecode.decoded i) rs := by
  apply snapshot_plan (footprint shares) (MycpuDecode.snapshot i) rs
    (MycpuDecode.snapshot_covers i rs config) _ 1000 _ _ (MycpuDecode.decode_certificate i)
  intro r value found
  by_cases compressed : MycpuDecode.compressed i = true
  · cases r <;> simp only [MycpuDecode.snapshot, compressed, ↓reduceIte, Option.some.injEq] at found
    all_goals first | contradiction | subst value
    exact ⟨shares.misa, by simp [footprint, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint, SupervisorRetirement.pcFootprint]⟩
  · cases r <;> simp only [MycpuDecode.snapshot, compressed, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at found
    all_goals first | contradiction | subst value
    · exact ⟨shares.environment, by simp [footprint, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint, SupervisorRetirement.pcFootprint]⟩
    · exact ⟨shares.privilege, by
        simp [footprint, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint, SupervisorRetirement.pcFootprint]⟩

theorem dispatch_plan (shares : Shares) (rs : RegisterFile) (privilege : rs .cur_privilege = .Supervisor)
    (disabled : SupervisorInterrupt.Disabled rs) :
    RegisterPlan.Returns (footprint shares) rs
      (PreSail.readReg .cur_privilege >>= dispatchInterrupt) none rs := by
  refine returns_bind (read_plan (fp := footprint shares) rs .cur_privilege
    shares.privilege (by
      simp [footprint, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint, SupervisorRetirement.pcFootprint])) ?_
  rw [privilege]
  apply widen_plan (MachCSL.Logic.SupervisorInterrupt.dispatch_plan (⟨shares.misa, .own 1, shares.enable, shares.delegation⟩) rs disabled)
  intro cell member
  simp only [MachCSL.Logic.SupervisorInterrupt.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [footprint, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint, SupervisorRetirement.pcFootprint]

theorem landing_plan (shares : Shares) (rs : RegisterFile) (clear : rs .elp = 0#1) :
    RegisterPlan.Returns (footprint shares) rs (is_landing_pad_expected ()) false rs := by
  unfold is_landing_pad_expected
  refine returns_bind (read_plan (fp := footprint shares) rs .elp shares.landing (by simp [footprint, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint, SupervisorRetirement.pcFootprint])) ?_
  rw [clear]
  exact pure_plan _ _ _

theorem zca_plan (shares : Shares) (rs : RegisterFile) (enabled : _get_Misa_C (rs .misa) = 1#1) :
    RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_Zca) true rs := by
  have c : RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_C) true rs := by
    unfold currentlyEnabled
    refine returns_bind (read_plan (fp := footprint shares) rs .misa shares.misa (by simp [footprint, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint])) ?_
    rw [enabled]
    simp only [hartSupports, beq_self_eq_true, Bool.and_self]
    exact pure_plan (footprint shares) rs _
  unfold currentlyEnabled
  refine returns_bind c ?_
  simp only [hartSupports, Bool.true_or, Bool.and_self]
  exact pure_plan (footprint shares) rs _

theorem decode_config (rs : RegisterFile) (i : Fin 14) (config : Config rs) : MycpuDecode.Config i rs := by
  unfold MycpuDecode.Config
  split
  · exact config.misa
  · exact ⟨config.privilege, config.environment⟩

theorem compressed_config (rs : RegisterFile) (config : Config rs) : _get_Misa_C (rs .misa) = 1#1 := by
  rw [config.misa]; rfl

private theorem execute_match_eq (value : ExecutionResult) (redirect : instruction → α)
    (ordinary : ExecutionResult → α) :
    execute_run.match_1 (fun _ => α) value redirect ordinary =
      executeTail.match_1 (fun _ => α) value redirect ordinary := by
  cases value <;> rfl

private theorem write_next (shares : Shares) (rs : RegisterFile) (i : Fin 14) :
    RegisterPlan.Returns (footprint shares) rs
      (PreSail.writeReg .nextPC (Sail.BitVec.addInt (rs .PC) (MycpuDecode.width i)))
      () (prepared i rs) :=
  .write (by simp [footprint, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint, SupervisorRetirement.pcFootprint]) (.pure ⟨rfl, rfl⟩)

private theorem instruction_size (i : Fin 14) :
    MycpuDecode.width i = if MycpuDecode.compressed i then 2 else 4 := by
  have check : ∀ i : Fin 14, MycpuDecode.width i = if MycpuDecode.compressed i then 2 else 4 := by decide
  exact check i

theorem prepare_prefix [Platform] (shares : Shares) (rs : RegisterFile) (i : Fin 14)
    (stepNo : Nat) (config : Config rs) :
    Prefix (footprint shares) rs (afterFetch stepNo (MycpuFetch.result i)) (executeTail i) (prepared i rs) := by
  have decode := decode_plan shares rs i (decode_config rs i config)
  have land := landing_plan shares rs config.landing
  have zca := zca_plan shares rs (compressed_config rs config)
  have pc := read_plan (fp := footprint shares) rs .PC (.own 1) (by
    simp [footprint, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint, SupervisorRetirement.pcFootprint])
  have write := write_next shares rs i
  by_cases rvc : MycpuDecode.compressed i = true
  · simp only [afterFetch, MycpuFetch.result, rvc, ↓reduceIte, ext_fetch_hook]
    simp only [MycpuDecode.decode, rvc, ↓reduceIte] at decode
    rw [run_lift_bind]
    refine Prefix.prefix decode ?_
    simp only [get_config_print_instr, Bool.false_eq_true, ↓reduceIte]
    rw [run_lift_bind]
    refine Prefix.prefix land ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [run_lift_bind]
    refine Prefix.prefix zca ?_
    simp only [↓reduceIte]
    rw [run_lift_bind]
    refine Prefix.prefix pc ?_
    rw [run_lift_bind]
    have width : MycpuDecode.width i = 2 := by rw [instruction_size, rvc]; rfl
    simp only [width] at write
    refine Prefix.prefix write ?_
    have equation := execute_run (MycpuDecode.decoded i) (zero_extend (m := 32) (BitVec.ofNat 16 (MycpuDecode.encoding i)))
    simp only [execute_match_eq] at equation
    rw [equation]
    have bits : zero_extend (m := 32) (BitVec.ofNat 16 (MycpuDecode.encoding i)) = instbits i := by
      have all : ∀ i : Fin 14, MycpuDecode.compressed i = true →
          zero_extend (m := 32) (BitVec.ofNat 16 (MycpuDecode.encoding i)) = instbits i := by decide
      exact all i rvc
    rw [bits]
    exact Prefix.done
  · simp only [afterFetch, MycpuFetch.result, rvc, Bool.false_eq_true, ↓reduceIte, ext_fetch_hook]
    simp only [MycpuDecode.decode, rvc, Bool.false_eq_true, ↓reduceIte] at decode
    rw [run_lift_bind]
    refine Prefix.prefix decode ?_
    simp only [get_config_print_instr, Bool.false_eq_true, ↓reduceIte]
    rw [run_lift_bind]
    refine Prefix.prefix land ?_
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [run_lift_bind]
    refine Prefix.prefix pc ?_
    rw [run_lift_bind]
    have width : MycpuDecode.width i = 4 := by rw [instruction_size]; simp [rvc]
    simp only [width] at write
    refine Prefix.prefix write ?_
    have equation := execute_run (MycpuDecode.decoded i) (zero_extend (m := 32) (BitVec.ofNat 32 (MycpuDecode.encoding i)))
    simp only [execute_match_eq] at equation
    rw [equation]
    have bits : zero_extend (m := 32) (BitVec.ofNat 32 (MycpuDecode.encoding i)) = instbits i := by
      with_unfolding_all rfl
    rw [bits]
    exact Prefix.done


end Xv6.Kernel.MycpuKptCycle
