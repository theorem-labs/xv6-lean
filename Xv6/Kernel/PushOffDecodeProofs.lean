import Xv6.Kernel.PushOffDecodeCertificates
import Xv6.Kernel.PushOffDecodePlan

namespace Xv6.Kernel.PushOffDecode
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

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



theorem unique (shares : Shares) (i : Index) : RegisterFootprint.Unique (footprint shares i) := by
  unfold footprint
  split <;> simp [RegisterFootprint.Unique]

theorem source_config (i : Index) (rs : RegisterFile)
    (misa : rs .misa = 0x800000000014112d#64)
    (priv : rs .cur_privilege = .Supervisor)
    (env : rs .menvcfg = 0xa000000000000000#64) : Config i rs := by
  unfold Config
  split
  · exact misa
  · exact ⟨priv, env⟩

theorem snapshot_covers (i : Index) (rs : RegisterFile) (config : Config i rs) :
    JalLoop.Covers (snapshot i) rs := by
  by_cases compressed : PushOffCode.compressed i = true
  · simp [Config, compressed] at config
    intro r value found
    cases r <;> simp only [snapshot, compressed, ↓reduceIte, Option.some.injEq] at found
    all_goals first | contradiction | subst value
    exact config
  · simp [Config, compressed] at config
    intro r value found
    cases r <;> simp only [snapshot, compressed, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at found
    all_goals first | contradiction | subst value
    · exact config.2
    · exact config.1

private theorem certified_plan (shares : Shares) (i : Index) (rs : RegisterFile)
    (config : Config i rs)
    (certificate : JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot i) 1000 (program i) =
      some (PushOffCode.decoded i)) :
    RegisterPlan.Returns (footprint shares i) rs (program i) (PushOffCode.decoded i) rs := by
  apply snapshot_plan (footprint shares i) (snapshot i) rs (snapshot_covers i rs config) _ 1000 _ _ certificate
  intro r value found
  by_cases compressed : PushOffCode.compressed i = true
  · cases r <;> simp only [snapshot, compressed, ↓reduceIte, Option.some.injEq] at found
    all_goals first | contradiction | subst value
    exact ⟨shares.misa, by simp [footprint, compressed]⟩
  · cases r <;> simp only [snapshot, compressed, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at found
    all_goals first | contradiction | subst value
    · exact ⟨shares.environment, by simp [footprint, compressed]⟩
    · exact ⟨shares.privilege, by simp [footprint, compressed]⟩

private theorem base_jal (shares : Shares) (i : Index) (rs : RegisterFile) (config : Config i rs)
    (imm : BitVec 21) (mode : PushOffCode.compressed i = false)
    (encoded : BitVec.ofNat 32 (PushOffCode.encoding i) = KptJal.encoding imm)
    (decoded : PushOffCode.decoded i = KptJal.instruction imm) (even : KptJal.Encodable imm) :
    RegisterPlan.Returns (footprint shares i) rs (program i) (PushOffCode.decoded i) rs := by
  have cfg : rs .cur_privilege = .Supervisor ∧ rs .menvcfg = 0xa000000000000000#64 := by
    simpa only [Config, mode, Bool.false_eq_true, ↓reduceIte] using config
  simp only [program, mode, Bool.false_eq_true, ↓reduceIte, encoded, decoded]
  exact jal_plan (footprint shares i) rs shares.privilege shares.environment
    (by simp [footprint, mode]) (by simp [footprint, mode]) cfg.1 cfg.2 imm even

theorem decode (shares : Shares) (i : Index) (rs : RegisterFile) (config : Config i rs) :
    RegisterPlan.Returns (footprint shares i) rs (program i) (PushOffCode.decoded i) rs := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certified_plan shares _ rs config decode00
  · exact certified_plan shares _ rs config decode01
  · exact certified_plan shares _ rs config decode02
  · exact certified_plan shares _ rs config decode03
  · exact certified_plan shares _ rs config decode04
  · exact certified_plan shares _ rs config decode05
  · exact certified_plan shares _ rs config decode06
  · exact base_jal shares _ rs config 3370#21 rfl
      (by change 0x52b000ef#32 = KptJal.encoding 3370#21; decide) rfl
      (by unfold KptJal.Encodable; decide)
  · exact certified_plan shares _ rs config decode08
  · exact certified_plan shares _ rs config decode09
  · exact base_jal shares _ rs config 3362#21 rfl
      (by change 0x523000ef#32 = KptJal.encoding 3362#21; decide) rfl
      (by unfold KptJal.Encodable; decide)
  · exact certified_plan shares _ rs config decode11
  · exact certified_plan shares _ rs config decode12
  · exact certified_plan shares _ rs config decode13
  · exact certified_plan shares _ rs config decode14
  · exact certified_plan shares _ rs config decode15
  · exact certified_plan shares _ rs config decode16
  · exact certified_plan shares _ rs config decode17
  · exact certified_plan shares _ rs config decode18
  · exact base_jal shares _ rs config 3342#21 rfl
      (by change 0x50f000ef#32 = KptJal.encoding 3342#21; decide) rfl
      (by unfold KptJal.Encodable; decide)
  · exact certified_plan shares _ rs config decode20
  · exact certified_plan shares _ rs config decode21
  · exact certified_plan shares _ rs config decode22
  · exact certified_plan shares _ rs config decode23

/-- Actual compressed execute branches, each returning one redirection.
The normalized body is not executed by this equality. -/
theorem compressed_expansion [Platform] (i : Index) (compressed : PushOffCode.compressed i = true) :
    execute (PushOffCode.decoded i) = (pure (.ExecuteAs (PushOffCode.normalized i)) : SailM ExecutionResult) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | contradiction

theorem compressed_plan [Platform] (fp : RegisterFootprint.Footprint) (i : Index)
    (rs : RegisterFile) (compressed : PushOffCode.compressed i = true) :
    RegisterPlan.Returns fp rs (execute (PushOffCode.decoded i)) (.ExecuteAs (PushOffCode.normalized i)) rs := by
  rw [compressed_expansion i compressed]
  exact .pure ⟨rfl, rfl⟩

theorem base_normalized (i : Index) (base : PushOffCode.compressed i = false) :
    PushOffCode.decoded i = PushOffCode.normalized i := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | contradiction

end Xv6.Kernel.PushOffDecode
