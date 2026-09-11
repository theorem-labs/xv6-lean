import Xv6.Kernel.MycpuDecodeCertificates

namespace Xv6.Kernel.MycpuDecode
open MachCSL.Machine LeanPaperStock.Functions MachCSL.Logic.EventWP
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem decode_certificate (i : Fin 14) :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot i) 1000 (decode i) = some (decoded i) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact decode00
  · exact decode01
  · exact decode02
  · exact decode03
  · exact decode04
  · exact decode05
  · exact decode06
  · exact decode07
  · exact decode08
  · exact decode09
  · exact decode10
  · exact decode11
  · exact decode12
  · exact decode13

theorem snapshot_covers (i : Fin 14) (rs : RegisterFile) (config : Config i rs) :
    JalLoop.Covers (snapshot i) rs := by
  by_cases h : compressed i = true
  · simp [Config, h] at config
    intro r value hv
    cases r <;> simp only [snapshot, h, ↓reduceIte, Option.some.injEq] at hv
    all_goals first | contradiction | subst value
    exact config
  · simp [Config, h] at config
    intro r value hv
    cases r <;> simp only [snapshot, h, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hv
    all_goals first | contradiction | subst value
    · exact config.2
    · exact config.1

theorem decode_plan (reads : ReadAllowed) (i : Fin 14) (rs : RegisterFile) (config : Config i rs) :
    Returns reads rs (decode i) (decoded i) rs :=
  JalLoopPlan.snapshotPlanRun_plan reads (fun _ _ => none)
    (fun _ _ _ h => by cases h) (snapshot i) rs (snapshot_covers i rs config)
    1000 (decode i) (decoded i) (decode_certificate i)

/-- The concrete source supervisor configuration supplies every row's decoder
premises while leaving all other register values arbitrary. -/
theorem source_config (i : Fin 14) (rs : RegisterFile)
    (misa : rs .misa = 0x800000000014112d#64)
    (priv : rs .cur_privilege = .Supervisor)
    (env : rs .menvcfg = 0xa000000000000000#64) : Config i rs := by
  unfold Config
  split
  · exact misa
  · exact ⟨priv, env⟩

theorem decode_supervisor_plan (reads : ReadAllowed) (i : Fin 14) (rs : RegisterFile)
    (misa : rs .misa = 0x800000000014112d#64)
    (priv : rs .cur_privilege = .Supervisor)
    (env : rs .menvcfg = 0xa000000000000000#64) :
    Returns reads rs (decode i) (decoded i) rs :=
  decode_plan reads i rs (source_config i rs misa priv env)

/-- Compressed decoding returns its compressed AST first. The actual execute
function then requests exactly the source's base-instruction expansion. -/
theorem compressed_expansion [Platform] (i : Fin 14) (rvc : compressed i = true) :
    execute (decoded i) = (pure (.ExecuteAs (normalized i)) : SailM ExecutionResult) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | contradiction

theorem compressed_expansion_plan [Platform] (reads : ReadAllowed) (i : Fin 14) (rs : RegisterFile)
    (rvc : compressed i = true) :
    Returns reads rs (execute (decoded i)) (.ExecuteAs (normalized i)) rs := by
  rw [compressed_expansion i rvc]
  exact pure_plan reads rs _

theorem base_normalized (i : Fin 14) (base : compressed i = false) : decoded i = normalized i := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | contradiction

/-- The source's AUIPC/ADDI pair computes this concrete cpus base. This checks
numeric instruction immediates, not an ELF symbol-table parser. -/
theorem cpus_literal :
    (address ⟨7, by decide⟩ + 0x11000#64) + BitVec.signExtend 64 (0xb20#12) =
      BitVec.ofInt 64 cpusAddress := rfl

end Xv6.Kernel.MycpuDecode
