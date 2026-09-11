import MachCSL.Machine.BootPmpProofs
import MachCSL.Logic.EventWPDefs

/-! Actual generated PMP checks under universal reset facts. These plans retain
configuration and address reads, with arbitrary address-vector contents. -/
namespace MachCSL.Machine.BootPmp
open MachCSL.Logic.EventWP LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem lift_except {reads : ReadAllowed} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : Returns reads rs program value rs) (ε : Type) :
    Returns reads rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change Returns reads rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact plan.bind (pure_plan reads rs _)

private theorem except_bind {reads : ReadAllowed} {program : SailME ε α}
    {next : α → SailME ε β} {rs : RegisterFile} {a : α} {b : β}
    (first : Returns reads rs program.run (.ok a) rs)
    (second : Returns reads rs (next a).run (.ok b) rs) :
    Returns reads rs (program >>= next).run (.ok b) rs := first.bind second

theorem read_address_plan (reads : ReadAllowed) (rs : RegisterFile) (off : Off rs)
    (n : Nat) (bound : n < 64) :
    Returns reads rs (pmpReadAddrReg n) (rs .pmpaddr_n)[n]! rs := by
  unfold pmpReadAddrReg
  refine (read_plan reads rs .pmpcfg_n (by decide)).bind ?_
  refine (read_plan reads rs .pmpaddr_n (by decide)).bind ?_
  have cfg : _get_Pmpcfg_ent_A (rs .pmpcfg_n)[n]! = 0#2 := by
    simpa only [_root_.getElem!_pos (rs Register.pmpcfg_n) n bound] using (off ⟨n, bound⟩).2
  rw [cfg]
  exact pure_plan reads rs _

theorem match_off_plan (reads : ReadAllowed) (rs : RegisterFile)
    (addr : physaddr) (width : BitVec 64) (cfg : BitVec 8) (current previous : BitVec 64)
    (off : _get_Pmpcfg_ent_A cfg = 0#2) :
    Returns reads rs (pmpMatchAddr addr width cfg current previous) .PMP_NoMatch rs := by
  cases addr
  unfold pmpMatchAddr
  rw [off]
  exact pure_plan reads rs _

private def checkRange : IntRange := ⟨0, 15, 1, by decide⟩

private theorem check_loop_plan (reads : ReadAllowed) (rs : RegisterFile) (ε : Type)
    (body : (i : Int) → i ∈ checkRange → Unit → SailME ε (ForInStep Unit))
    (law : ∀ i hi, Returns reads rs (body i hi ()).run (.ok (.yield ())) rs)
    (remaining i : Nat) (bound : remaining + i = 16) :
    Returns reads rs (IntRange.forIn'.loop checkRange body () (i : Int) (by simp [checkRange])).run (.ok ()) rs := by
  induction remaining generalizing i with
  | zero =>
    have eq : i = 16 := by omega
    subst i
    rw [IntRange.forIn'.loop.eq_1]
    rw [dif_neg (show ¬ ((16 : Nat) : Int) ∈ checkRange by decide)]
    exact pure_plan reads rs _
  | succ remaining ih =>
    have inside : (i : Int) ∈ checkRange := by simp [checkRange, Membership.mem]; omega
    rw [IntRange.forIn'.loop.eq_1, dif_pos inside]
    refine except_bind (law i inside) ?_
    simpa only [checkRange, Int.natCast_add, Int.natCast_one] using ih (i + 1) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem check_off_plan (reads : ReadAllowed) (rs : RegisterFile) (off : Off rs)
    (addr : physaddr) (width : Nat) (access : MemoryAccessType mem_payload) :
    Returns reads rs (pmpCheck addr width access .Machine) none rs := by
  unfold pmpCheck _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [show (sys_pmp_count == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Returns.bind (value := Except.ok none) ?_ (pure_plan reads rs _)
  refine except_bind (a := ()) ?_ (pure_plan reads rs _)
  apply check_loop_plan reads rs (Option ExceptionType) _ ?_ 16 0 rfl
  intro i inside
  have low : 0 ≤ i := by have := inside; simp [checkRange, Membership.mem] at this; omega
  have high : i < 16 := by have := inside; simp [checkRange, Membership.mem] at this; omega
  dsimp only
  split
  all_goals
    first
    | refine except_bind (lift_except (read_address_plan reads rs off (i - 1).toNat (by omega)) _) ?_
    | refine except_bind (pure_plan reads rs _) ?_
    refine except_bind (lift_except (read_plan reads rs .pmpcfg_n (by decide)) _) ?_
    refine except_bind (a := (rs .pmpcfg_n)[i]!) (pure_plan reads rs _) ?_
    refine except_bind (lift_except (read_address_plan reads rs off i.toNat (by omega)) _) ?_
    refine except_bind (lift_except (match_off_plan reads rs addr _ _ _ _ ((off_int rs off i low (by omega)).2)) _) ?_
    exact pure_plan reads rs _

/-- Universal boot specialization of the actual PMP event plan. -/
theorem bootFacts_check_plan (reads : ReadAllowed) (image : BootImage) (g : State)
    (facts : BootFacts image g) (cpu : CPU) (addr : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) :
    Returns reads (g.registers cpu) (pmpCheck addr width access .Machine) none (g.registers cpu) :=
  check_off_plan reads (g.registers cpu) (bootFacts_off image g facts cpu) addr width access

end MachCSL.Machine.BootPmp
