import MachCSL.Logic.EventWPDefs
import MachCSL.Machine.JalLoopFetchEval

/-! Kernel-checked plan certificates. Successful evaluation proves that all
accessed registers are CPU-owned; hardware-pin events are rejected rather than
silently assigning them a fixed value. These are proof tools, not semantics. -/
namespace MachCSL.Machine.JalLoopPlan
open MachCSL.Logic.EventWP

/-- A register certificate rejects both asynchronously modified pin keys. -/
def registerPlanRun : Nat → SailM α → RegisterFile → Option (α × RegisterFile)
  | 0, _, _ => none
  | _ + 1, .pure value, rs => some (value, rs)
  | fuel + 1, .impure event k, rs => match event with
    | .readReg r => if IsOwned r then registerPlanRun fuel (k (rs r)) rs else none
    | .writeReg r value => if IsOwned r then
        registerPlanRun fuel (k ()) (Sail.Registers.write rs r value) else none
    | _ => none

theorem registerPlanRun_plan (reads : ReadAllowed) (fuel : Nat) (program : SailM α)
    (before after : RegisterFile) (value : α)
    (success : registerPlanRun fuel program before = some (value, after)) :
    Returns reads before program value after := by
  induction fuel generalizing program before with
  | zero => simp [registerPlanRun] at success
  | succ fuel ih =>
    cases program with
    | pure result =>
      simp only [registerPlanRun, Option.some.injEq, Prod.mk.injEq] at success
      obtain ⟨rfl, rfl⟩ := success
      exact pure_plan reads _ _
    | impure event k =>
      cases event <;> simp only [registerPlanRun] at success
      all_goals first | contradiction | skip
      case readReg r =>
        split at success
        · rename_i owned
          exact .readOwned owned (ih _ _ success)
        · contradiction
      case writeReg r v =>
        split at success
        · rename_i owned
          exact .writeOwned owned (ih _ _ success)
        · contradiction

/-- A RAM oracle is an explicit partial table. Soundness requires resources for
all returned entries, allowing a four-byte code table instead of all of RAM. -/
abbrev ReadOracle := (n : Nat) → Logic.MemoryReadWP.ReadRequest n → Option (BitVec (8 * n))

def snapshotPlanRun (oracle : ReadOracle) (snapshot : JalLoop.Snapshot) :
    Nat → SailM α → Option α
  | 0, _ => none
  | _ + 1, .pure value => some value
  | fuel + 1, .impure event k => match event with
    | .readReg r => if IsOwned r then
        (snapshot r).bind fun value => snapshotPlanRun oracle snapshot fuel (k value)
      else none
    | .readMem n req =>
      if deviceAddress req.pa || accessExclusive req.access_kind then none else
      (oracle n req).bind fun word => snapshotPlanRun oracle snapshot fuel (k (.Ok (word, none)))
    | _ => none

theorem snapshotPlanRun_plan (reads : ReadAllowed) (oracle : ReadOracle)
    (allowed : ∀ n req word, oracle n req = some word → reads n req word)
    (snapshot : JalLoop.Snapshot) (rs : RegisterFile) (covered : JalLoop.Covers snapshot rs)
    (fuel : Nat) (program : SailM α) (value : α)
    (success : snapshotPlanRun oracle snapshot fuel program = some value) :
    Returns reads rs program value rs := by
  induction fuel generalizing program with
  | zero => simp [snapshotPlanRun] at success
  | succ fuel ih =>
    cases program with
    | pure result =>
      simp only [snapshotPlanRun, Option.some.injEq] at success
      subst result
      exact pure_plan reads rs value
    | impure event k =>
      cases event <;> simp only [snapshotPlanRun] at success
      all_goals first | contradiction | skip
      case readReg r =>
        split at success
        · rename_i owned
          cases hs : snapshot r with
          | none => simp [hs] at success
          | some actual =>
            simp only [hs, Option.bind_some] at success
            have rest := ih _ success
            rw [← covered r actual hs] at rest
            exact .readOwned owned rest
        · contradiction
      case readMem n req =>
        split at success
        · contradiction
        · rename_i hgate
          have gate : deviceAddress req.pa = false ∧ accessExclusive req.access_kind = false := by
            simpa using hgate
          cases hw : oracle n req with
          | none => simp [hw] at success
          | some word =>
            simp only [hw, Option.bind_some] at success
            exact .readMem gate.1 gate.2 (allowed n req word hw) (ih _ success)

theorem covers_write (snapshot : JalLoop.Snapshot) (rs : RegisterFile)
    (covered : JalLoop.Covers snapshot rs) (r : Register) (value : RegisterType r)
    (unused : snapshot r = none) : JalLoop.Covers snapshot (Sail.Registers.write rs r value) := by
  intro key actual found
  by_cases same : r = key
  · subst key
    rw [unused] at found
    contradiction
  · rw [Sail.Registers.write_other rs r key value same]
    exact covered key actual found

end MachCSL.Machine.JalLoopPlan
