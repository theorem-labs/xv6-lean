import MachCSL.Machine.JalLoopPlan
import MachCSL.Machine.JalLoopPlanInstruction
import MachCSL.Machine.BootUniversalProofs

/-! Actual generated cycle composition. The fetch premise is a universally
branching event plan, not an existential sequential trace. -/
namespace MachCSL.Logic.EventWP
open MachCSL.Machine

theorem Returns.liftExcept {reads : ReadAllowed} {program : SailM α}
    {before after : RegisterFile} {value : α}
    (plan : Returns reads before program value after) (ε : Type) :
    Returns reads before (monadLift program : SailME ε α).run (.ok value) after := by
  change Returns reads before (program >>= fun a => pure (Except.ok a)) (.ok value) after
  exact plan.bind (pure_plan reads after _)

theorem Returns.exceptBind {reads : ReadAllowed} {program : SailME ε α}
    {next : α → SailME ε β} {before middle after : RegisterFile} {a : α} {b : β}
    (first : Returns reads before program.run (.ok a) middle)
    (second : Returns reads middle (next a).run (.ok b) after) :
    Returns reads before (program >>= next).run (.ok b) after :=
  first.bind second

end MachCSL.Logic.EventWP

namespace MachCSL.Machine.JalLoopPlan
open MachCSL.Logic.EventWP LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

abbrev Static := BootUniversal.StaticBoot jalImage.vector

theorem active_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (fetched : Returns reads rs (fetch ()) (.F_Base 0x6f#32) rs) :
    Returns reads rs (run_hart_active 0) (.Step_Execute (.Retire_Success (), 0x6f#32)) rs := by
  have restored : Sail.Registers.write
      (Sail.Registers.write rs .nextPC (_root_.Sail.BitVec.addInt (rs .PC) 4))
      .nextPC jalImage.vector = rs := by
    rw [Sail.Registers.write_overwrite, ← static.nextPC, Sail.Registers.write_current]
  unfold run_hart_active _root_.Sail.SailME.run PreSail.PreSailME.run
  refine Returns.bind (value := Except.ok (.Step_Execute (.Retire_Success (), 0x6f#32))) ?_
    (pure_plan reads rs _)
  refine (read_plan reads rs .cur_privilege (by decide)).bind ?_
  change Returns reads rs (_ >>= _) _ _
  rw [static.privilege]
  refine ((dispatchInterrupt_plan reads rs static.mstatus).liftExcept _root_.Step).bind ?_
  refine (fetched.liftExcept _root_.Step).bind ?_
  refine ((decode_plan reads rs static.privilege static.mseccfg).liftExcept _root_.Step).bind ?_
  simp only [show get_config_print_instr () = false from rfl, Bool.false_eq_true, ↓reduceIte]
  unfold is_landing_pad_expected
  refine (read_plan reads rs .elp (by decide)).bind ?_
  rw [static.elp]
  simp only [show (0#1 == landing_pad_bits_backwards .LP_EXPECTED) = false by decide]
  refine (read_plan reads rs .PC (by decide)).bind ?_
  refine (write_plan reads rs .nextPC (_root_.Sail.BitVec.addInt (rs .PC) 4) (by decide)).bind ?_
  let middle := Sail.Registers.write rs .nextPC (_root_.Sail.BitVec.addInt (rs .PC) 4)
  have pc : middle .PC = jalImage.vector := by simpa [middle, Sail.Registers.write] using static.pc
  have misa : middle .misa = 0x800000000014112d#64 := by
    simpa [middle, Sail.Registers.write] using static.misa
  simp only [ExceptT.bindCont]
  apply Returns.exceptBind (a := .Retire_Success ())
  · apply Returns.exceptBind
      ((execute_JAL_plan reads middle pc misa).liftExcept _root_.Step)
    rw [show Sail.Registers.write middle .nextPC jalImage.vector = rs from restored]
    exact pure_plan reads rs _
  · exact pure_plan reads rs _

def retireEnabled (rs : RegisterFile) : Bool :=
  (_get_Counterin_IR (rs .mcountinhibit) == 0#1) &&
    (counter_priv_filter_bit (rs .minstretcfg) (rs .cur_privilege) == 0#1)

def enableAfter (rs : RegisterFile) : RegisterFile :=
  Sail.Registers.write rs .minstret_increment (retireEnabled rs)

def retireAfter (rs : RegisterFile) : RegisterFile :=
  if retireEnabled rs then
    Sail.Registers.write (enableAfter rs) .minstret (_root_.Sail.BitVec.addInt (rs .minstret) 1)
  else enableAfter rs

theorem static_enable (rs : RegisterFile) (static : Static rs) : Static (enableAfter rs) :=
  ⟨static.pc, static.nextPC, static.misa, static.mstatus, static.mie, static.mideleg,
    static.menvcfg, static.elp, static.mseccfg, static.privilege, static.hartState, static.pma, static.htif⟩

theorem tick_pc_plan (reads : ReadAllowed) (rs : RegisterFile) (pc : rs .nextPC = rs .PC) :
    Returns reads rs (tick_pc ()) () rs := by
  unfold tick_pc
  refine (read_plan reads rs .nextPC (by decide)).bind ?_
  have write : Sail.Registers.write rs .PC (rs .nextPC) = rs := by
    rw [pc, Sail.Registers.write_current]
  have written := write_plan reads rs .PC (rs .nextPC) (by decide)
  rw [write] at written
  refine written.bind ?_
  refine (read_plan reads rs .PC (by decide)).bind ?_
  exact pure_plan reads rs ()

/-- Arbitrary counter-inhibit and privilege-filter settings are retained.
Both retirement branches and modular overflow are covered by the actual model. -/
theorem try_step_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (fetched : Returns reads (enableAfter rs) (fetch ()) (.F_Base 0x6f#32) (enableAfter rs)) :
    Returns reads rs (try_step 0 false) false (retireAfter rs) := by
  unfold try_step
  refine (read_plan reads rs .cur_privilege (by decide)).bind ?_
  refine (should_inc_minstret_plan reads rs (rs .cur_privilege)).bind ?_
  refine (write_plan reads rs .minstret_increment (retireEnabled rs) (by decide)).bind ?_
  let middle := enableAfter rs
  have s : Static middle := static_enable rs static
  have active : middle .hart_state = .HART_ACTIVE () := s.hartState
  refine (read_plan reads middle .hart_state (by decide)).bind ?_
  rw [active]
  refine (active_plan reads middle s fetched).bind ?_
  refine (read_plan reads middle .hart_state (by decide)).bind ?_
  rw [active]
  refine (read_plan reads middle .hart_state (by decide)).bind ?_
  rw [active]
  refine (tick_pc_plan reads middle (s.nextPC.trans s.pc.symm)).bind ?_
  refine (read_plan reads middle .minstret_increment (by decide)).bind ?_
  change Returns reads middle
    (if retireEnabled rs then
      (do Sail.ConcurrencyInterfaceV1.Free.PreSail.writeReg .minstret
            (_root_.Sail.BitVec.addInt (← Sail.ConcurrencyInterfaceV1.Free.PreSail.readReg .minstret) 1)
          pure false)
     else pure false) false (retireAfter rs)
  by_cases enabled : retireEnabled rs = true
  · simp only [enabled, ↓reduceIte, retireAfter]
    refine (read_plan reads middle .minstret (by decide)).bind ?_
    refine (write_plan reads middle .minstret (_root_.Sail.BitVec.addInt (middle .minstret) 1) (by decide)).bind ?_
    exact pure_plan reads _ false
  · simp only [enabled, retireAfter]
    exact pure_plan reads middle false

theorem static_retire (rs : RegisterFile) (static : Static rs) : Static (retireAfter rs) := by
  unfold retireAfter
  split
  · exact ⟨static.pc, static.nextPC, static.misa, static.mstatus, static.mie, static.mideleg,
      static.menvcfg, static.elp, static.mseccfg, static.privilege, static.hartState, static.pma, static.htif⟩
  · exact static_enable rs static

theorem static_clock (rs : RegisterFile) (static : Static rs) : Static (clockAfter rs) := by
  unfold clockAfter timeAfter counterAfter
  split
  · exact ⟨static.pc, static.nextPC, static.misa, static.mstatus, static.mie, static.mideleg,
      static.menvcfg, static.elp, static.mseccfg, static.privilege, static.hartState, static.pma, static.htif⟩
  · exact ⟨static.pc, static.nextPC, static.misa, static.mstatus, static.mie, static.mideleg,
      static.menvcfg, static.elp, static.mseccfg, static.privilege, static.hartState, static.pma, static.htif⟩

def cycleAfter (tick : Bool) (rs : RegisterFile) : RegisterFile :=
  if tick then clockAfter (retireAfter rs) else retireAfter rs

theorem cycle_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile) (static : Static rs)
    (tick : Bool)
    (fetched : Returns reads (enableAfter rs) (fetch ()) (.F_Base 0x6f#32) (enableAfter rs)) :
    Returns reads rs (cycle tick) () (cycleAfter tick rs) := by
  unfold cycle
  refine (try_step_plan reads rs static fetched).bind ?_
  cases tick
  · exact pure_plan reads _ ()
  · exact tick_clock_plan reads (retireAfter rs) (static_retire rs static).menvcfg

theorem static_cycle (tick : Bool) (rs : RegisterFile) (static : Static rs) :
    Static (cycleAfter tick rs) := by
  cases tick
  · exact static_retire rs static
  · exact static_clock _ (static_retire rs static)

end MachCSL.Machine.JalLoopPlan
