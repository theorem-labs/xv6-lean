import MachCSL.Machine.BootPmpProgram
import MachCSL.Machine.BootUniversalProofs
namespace MachCSL.Machine.BootPmp
open LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem clear_lock (entry : BitVec 8) : _get_Pmpcfg_ent_L (clearEntry entry) = 0#1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [clearEntry, _get_Pmpcfg_ent_L, _update_Pmpcfg_ent_L, _update_Pmpcfg_ent_A,
    pmpAddrMatchType_encdec_forwards, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  intro h
  subst i
  simp only [show (127#8).getLsbD (7+0) = false from rfl, Bool.false_eq_true, false_implies]

theorem clear_addr (entry : BitVec 8) : _get_Pmpcfg_ent_A (clearEntry entry) = 0#2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [clearEntry, _get_Pmpcfg_ent_A, _update_Pmpcfg_ent_L, _update_Pmpcfg_ent_A,
    pmpAddrMatchType_encdec_forwards, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  intro h
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · simp only [show (231#8).getLsbD (3+0) = false from rfl, Bool.false_eq_true, false_implies, implies_true]
  · simp only [show (231#8).getLsbD (3+1) = false from rfl, Bool.false_eq_true, false_implies, implies_true]

theorem get_int (v : Vector (BitVec 8) 64) (i : Nat) (hi : i < 64) : v[(i : Int)]! = v[i] := by
  simp [GetElem?.getElem!, hi]

/-- Generic loop invariant, not 64 separately evaluated boot runs. -/
theorem prefix_lookup (entries : Vector (BitVec 8) 64) (n i : Nat) (hi : i < 64) :
    (resetPrefix n entries)[i] = if i < n then clearEntry entries[i] else entries[i] := by
  induction n with
  | zero => simp [resetPrefix]
  | succ n ih =>
    simp only [resetPrefix, Vector.getElem_set! hi]
    by_cases eq : n = i
    · subst n
      rw [if_pos rfl, get_int _ i hi, ih]
      simp
    · rw [if_neg eq, ih]
      have : (i < n + 1) = (i < n) := by apply propext; omega
      simp only [this]
theorem reset_pmp_eq : reset_pmp () = resetLoop 0 >>= fun _ => pure () := rfl

private theorem body_run (bus : Bus Device) (i : Nat) (hi : (i : Int) ∈ resetRange)
    (before after : ViewState Device) (value : ForInStep Unit)
    (run : Run bus (resetBody (i : Int) hi ()) before value after) :
    value = .yield () ∧ after = {before with registers := (Sail.Registers.write before.registers .pmpcfg_n
      ((before.registers .pmpcfg_n).set! i (clearEntry (before.registers .pmpcfg_n)[(i : Int)]!)))} := by
  apply BootUniversal.registerRun_unique bus 4 _ before.registers _ (.yield ()) value before.memory before.devices after _ run
  rfl

/-- Structural induction through the generated inclusive IntRange loop. -/
theorem loop_run (bus : Bus Device) (remaining i : Nat) (bound : remaining + i = 64)
    (original : Vector (BitVec 8) 64) (before after : ViewState Device)
    (cfg : before.registers .pmpcfg_n = resetPrefix i original)
    (run : Run bus (resetLoop i) before () after) :
    after.registers .pmpcfg_n = resetPrefix 64 original ∧
      after.registers .pmpaddr_n = before.registers .pmpaddr_n := by
  induction remaining generalizing i before with
  | zero =>
    have eq : i = 64 := by omega
    subst i
    unfold resetLoop at run
    rw [IntRange.forIn'.loop.eq_1] at run
    have outside : ¬ ((64 : Nat) : Int) ∈ resetRange := by decide
    rw [dif_neg outside] at run
    have same := (run_pure bus () before after).mp run
    subst after
    exact ⟨cfg, rfl⟩
  | succ remaining ih =>
    have inside : (i : Int) ∈ resetRange := by simp [resetRange, Membership.mem]; omega
    unfold resetLoop at run
    rw [IntRange.forIn'.loop.eq_1, dif_pos inside] at run
    obtain ⟨value, middle, body, rest⟩ := (run_bind bus _ _ before after ()).mp run
    obtain ⟨rfl, rfl⟩ := body_run bus i inside before middle value body
    have next : Run bus (resetLoop (i + 1))
        {before with registers := (Sail.Registers.write before.registers .pmpcfg_n
          ((before.registers .pmpcfg_n).set! i (clearEntry (before.registers .pmpcfg_n)[(i : Int)]!)))}
        () after := by
      simpa only [resetLoop, resetRange, Int.natCast_add, Int.natCast_one] using rest
    have updated : (Sail.Registers.write before.registers .pmpcfg_n
        ((before.registers .pmpcfg_n).set! i (clearEntry (before.registers .pmpcfg_n)[(i : Int)]!))) .pmpcfg_n =
        resetPrefix (i + 1) original := by
      change (before.registers .pmpcfg_n).set! i (clearEntry (before.registers .pmpcfg_n)[(i : Int)]!) = _
      rw [cfg]
      rfl
    obtain ⟨done, preserved⟩ := ih (i + 1) (by omega) _ updated next
    exact ⟨done, preserved⟩

theorem run_reset (bus : Bus Device) (before after : ViewState Device)
    (run : Run bus (reset_pmp ()) before () after) :
    after.registers .pmpcfg_n = resetPrefix 64 (before.registers .pmpcfg_n) ∧
      after.registers .pmpaddr_n = before.registers .pmpaddr_n := by
  rw [reset_pmp_eq] at run
  obtain ⟨value, middle, loop, tail⟩ := (run_bind bus _ _ before after ()).mp run
  have same := (run_pure bus () middle after).mp tail
  subst after
  cases value
  exact loop_run bus 64 0 rfl (before.registers .pmpcfg_n) before middle rfl loop

private def pmpProjection (rs : RegisterFile) := (rs .pmpcfg_n, rs .pmpaddr_n)

private theorem before_projection (before : RegisterFile) (vector hart : BitVec 64) :
    (registerRun 10000 (beforePmp vector hart) before).map (fun (_, rs) => pmpProjection rs) =
      some (pmpProjection before) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem after_projection (before : RegisterFile) :
    (registerRun 10000 afterPmp before).map (fun (_, rs) => pmpProjection rs) =
      some (pmpProjection before) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem run_preserves (bus : Bus Device) (program : SailM Unit)
    (projection : ∀ before, (registerRun 10000 program before).map (fun (_, rs) => pmpProjection rs) =
      some (pmpProjection before)) (before after : ViewState Device)
    (run : Run bus program before () after) : pmpProjection after.registers = pmpProjection before.registers := by
  have projected := projection before.registers
  cases eq : registerRun 10000 program before.registers with
  | none =>
    simp only [eq, Option.map_none] at projected
    cases projected
  | some pair =>
    obtain ⟨value, registers⟩ := pair
    cases value
    have unique := BootUniversal.registerRun_unique bus 10000 program before.registers registers () () before.memory before.devices after eq run
    have same := congrArg ViewState.registers unique.2
    rw [same]
    rw [eq] at projected
    exact Option.some.inj projected

/-- Every completed actual boot, at arbitrary original registers, resets exactly
A/L in every PMP entry and preserves the arbitrary PMP address vector. -/
theorem run_boot (bus : Bus Device) (before after : ViewState Device) (vector hart : BitVec 64)
    (run : Run bus (bootProgram vector hart pmaBoot) before () after) :
    after.registers .pmpcfg_n = resetPrefix 64 (before.registers .pmpcfg_n) ∧
      after.registers .pmpaddr_n = before.registers .pmpaddr_n := by
  rw [program_eq] at run
  obtain ⟨u, middle, first, rest⟩ := (run_bind bus _ _ before after ()).mp run
  cases u
  obtain ⟨u, last, reset, tail⟩ := (run_bind bus _ _ middle after ()).mp rest
  cases u
  have pre := run_preserves bus (beforePmp vector hart) (fun rs => before_projection rs vector hart) before middle first
  have post := run_preserves bus afterPmp after_projection last after tail
  have reset := run_reset bus middle last reset
  have preCfg := congrArg Prod.fst pre
  have preAddr := congrArg Prod.snd pre
  have postCfg := congrArg Prod.fst post
  have postAddr := congrArg Prod.snd post
  exact ⟨postCfg.trans (reset.1.trans (congrArg (resetPrefix 64) preCfg)), postAddr.trans (reset.2.trans preAddr)⟩

theorem run_off (bus : Bus Device) (before after : ViewState Device) (vector hart : BitVec 64)
    (run : Run bus (bootProgram vector hart pmaBoot) before () after) : Off after.registers := by
  have cfg := (run_boot bus before after vector hart run).1
  intro i
  rw [cfg, prefix_lookup _ 64 i.val i.isLt, if_pos i.isLt]
  exact ⟨clear_lock _, clear_addr _⟩

theorem bootFacts_off (image : BootImage) (g : State) (facts : BootFacts image g) (cpu : CPU) :
    Off (g.registers cpu) := by
  obtain ⟨before, after, run, eq⟩ := facts.2.2.1 cpu
  rw [eq]
  exact run_off Devices.bus ⟨before, Memory.empty, Devices.initial⟩ ⟨after, Memory.empty, Devices.initial⟩
    image.vector (BitVec.ofNat 64 cpu.val) run

theorem off_locked (rs : RegisterFile) (off : Off rs) (i : Fin 64) :
    pmpLocked (rs .pmpcfg_n)[i.val] = false := by
  simp [pmpLocked, (off i).1]

theorem off_mode (rs : RegisterFile) (off : Off rs) (i : Fin 64) :
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (rs .pmpcfg_n)[i.val]) = .OFF := by
  rw [(off i).2]
  rfl

theorem off_int (rs : RegisterFile) (off : Off rs) (i : Int) (low : 0 ≤ i) (high : i < 64) :
    _get_Pmpcfg_ent_L (rs .pmpcfg_n)[i]! = 0#1 ∧
      _get_Pmpcfg_ent_A (rs .pmpcfg_n)[i]! = 0#2 := by
  have n : i.toNat < 64 := by omega
  have cast : (i.toNat : Int) = i := Int.toNat_of_nonneg low
  rw [← cast, get_int _ i.toNat n]
  exact off ⟨i.toNat, n⟩

/-- Only bit 7 (L) and bits 4:3 (A) are cleared. -/
theorem clear_mask (entry : BitVec 8) : clearEntry entry = entry &&& 0x67#8 := by
  change (127#8 &&& ((231#8 &&& entry) ||| 0#8)) ||| 0#8 = _
  simp only [BitVec.or_zero, ← BitVec.and_assoc]
  rw [show (127#8 &&& 231#8) = 0x67#8 from rfl, BitVec.and_comm]

theorem clear_other (entry : BitVec 8) (i : Nat) (hi : i < 8)
    (notA0 : i ≠ 3) (notA1 : i ≠ 4) (notL : i ≠ 7) :
    (clearEntry entry).getLsbD i = entry.getLsbD i := by
  rw [clear_mask, BitVec.getLsbD_and]
  have bit : (0x67#8).getLsbD i = true := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [bit, Bool.and_true]

end MachCSL.Machine.BootPmp
