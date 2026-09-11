import MachCSL.Logic.EventWPDefs
import MachCSL.Machine.JalLoopReadOnly
import MachCSL.Machine.JalLoopClock

/-! Universally branching event plans for the actual model. Pin results vary
independently at every read; no full-RF ownership or whole-cycle atomicity is used. -/
namespace MachCSL.Machine.JalLoopPlan
open MachCSL.Logic.EventWP
open LeanPaperStock.Functions

/-- The generic read-only tree includes EVERY pin-result combination. -/
theorem readOnly_plan (reads : ReadAllowed) (rs : RegisterFile) {program : SailM α}
    (readonly : JalLoop.ReadOnly program) :
    ExecPlan reads rs program (fun _ after => after = rs) := by
  induction readonly with
  | pure value => exact .pure rfl
  | read r k _ ih =>
    by_cases pin : IsPin r
    · exact .readPin pin ih
    · exact .readOwned pin (ih (rs r))

theorem readOnly_unit_plan (reads : ReadAllowed) (rs : RegisterFile) {program : SailM Unit}
    (readonly : JalLoop.ReadOnly program) : Returns reads rs program () rs :=
  (readOnly_plan reads rs readonly).mono fun value _ same => by cases value; exact ⟨rfl, same⟩

theorem mip_callback_plan (reads : ReadAllowed) (rs : RegisterFile) :
    Returns reads rs (do
      let value ← read_mip .IncludePlatformInterrupts
      csr_name_write_callback "mip" value) () rs :=
  readOnly_unit_plan reads rs
    (JalLoop.ReadOnly.bind (JalLoop.read_mip_readOnly .IncludePlatformInterrupts)
      JalLoop.mip_callback_readOnly)

private theorem sstc_pure : currentlyEnabled .Ext_Sstc = pure (hartSupports .Ext_Sstc) := by
  unfold currentlyEnabled
  rfl

theorem clint_dispatch_plan (reads : ReadAllowed) (rs : RegisterFile) (env : rs .menvcfg = 0#64) :
    Returns reads rs (clint_dispatch false) () (JalLoop.clintAfter rs) := by
  unfold clint_dispatch
  refine (read_plan reads rs .mip (by decide)).bind ?_
  refine (read_plan reads rs .mip (by decide)).bind ?_
  refine (read_plan reads rs .mtimecmp (by decide)).bind ?_
  refine (read_plan reads rs .mtime (by decide)).bind ?_
  refine (write_plan reads rs .mip (JalLoop.timerPending rs) (by decide)).bind ?_
  rw [sstc_pure]
  refine (read_plan reads (JalLoop.clintAfter rs) .menvcfg (by decide)).bind ?_
  have env' : JalLoop.clintAfter rs .menvcfg = 0#64 := by
    simpa [JalLoop.clintAfter, Sail.Registers.write] using env
  rw [env']
  simp only [show (_get_MEnvcfg_STCE 0#64 == 1#1) = false by decide,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    show get_config_print_clint () = false from rfl]
  refine (read_plan reads (JalLoop.clintAfter rs) .mip (by decide)).bind ?_
  simp only [Bool.or_false]
  change Returns reads (JalLoop.clintAfter rs)
    (if rs .mip != JalLoop.clintAfter rs .mip then
      (do let value ← read_mip .IncludePlatformInterrupts
          csr_name_write_callback "mip" value)
     else pure ()) () (JalLoop.clintAfter rs)
  split
  · exact mip_callback_plan reads _
  · exact pure_plan reads _ ()

/-- Exact source guard, retaining arbitrary inhibit/configuration and privilege. -/
def cycleEnabled (rs : RegisterFile) : Bool :=
  (_get_Counterin_CY (rs .mcountinhibit) == 0#1) &&
    (counter_priv_filter_bit (rs .mcyclecfg) (rs .cur_privilege) == 0#1)

def counterAfter (rs : RegisterFile) : RegisterFile :=
  if cycleEnabled rs then
    Sail.Registers.write rs .mcycle (_root_.Sail.BitVec.addInt (rs .mcycle) 1)
  else rs

def timeAfter (rs : RegisterFile) : RegisterFile :=
  Sail.Registers.write rs .mtime (_root_.Sail.BitVec.addInt (rs .mtime) 1)

def clockAfter (rs : RegisterFile) : RegisterFile :=
  JalLoop.clintAfter (timeAfter (counterAfter rs))

theorem should_inc_mcycle_plan (reads : ReadAllowed) (rs : RegisterFile) (priv : Privilege) :
    Returns reads rs (should_inc_mcycle priv)
      ((_get_Counterin_CY (rs .mcountinhibit) == 0#1) &&
        (counter_priv_filter_bit (rs .mcyclecfg) priv == 0#1)) rs := by
  unfold should_inc_mcycle
  refine (read_plan reads rs .mcountinhibit (by decide)).bind ?_
  refine (read_plan reads rs .mcyclecfg (by decide)).bind ?_
  exact pure_plan reads rs _

theorem should_inc_minstret_plan (reads : ReadAllowed) (rs : RegisterFile) (priv : Privilege) :
    Returns reads rs (should_inc_minstret priv)
      ((_get_Counterin_IR (rs .mcountinhibit) == 0#1) &&
        (counter_priv_filter_bit (rs .minstretcfg) priv == 0#1)) rs := by
  unfold should_inc_minstret
  refine (read_plan reads rs .mcountinhibit (by decide)).bind ?_
  refine (read_plan reads rs .minstretcfg (by decide)).bind ?_
  exact pure_plan reads rs _

theorem time_dispatch_plan (reads : ReadAllowed) (rs : RegisterFile)
    (env : rs .menvcfg = 0#64) :
    Returns reads rs (do
      Sail.ConcurrencyInterfaceV1.Free.PreSail.writeReg .mtime
        (_root_.Sail.BitVec.addInt (← Sail.ConcurrencyInterfaceV1.Free.PreSail.readReg .mtime) 1)
      clint_dispatch false) () (JalLoop.clintAfter (timeAfter rs)) := by
  refine (read_plan reads rs .mtime (by decide)).bind ?_
  refine (write_plan reads rs .mtime (_root_.Sail.BitVec.addInt (rs .mtime) 1) (by decide)).bind ?_
  apply clint_dispatch_plan
  simpa [timeAfter, Sail.Registers.write] using env

/-- Every actual clock event is covered, including arbitrary counter-filter
settings, wraparound, timer comparisons and independently changing callback pins. -/
theorem tick_clock_plan (reads : ReadAllowed) (rs : RegisterFile)
    (env : rs .menvcfg = 0#64) :
    Returns reads rs (tick_clock ()) () (clockAfter rs) := by
  unfold tick_clock
  refine (read_plan reads rs .cur_privilege (by decide)).bind ?_
  refine (should_inc_mcycle_plan reads rs (rs .cur_privilege)).bind ?_
  by_cases enabled : cycleEnabled rs = true
  · simp only [cycleEnabled] at enabled
    simp only [clockAfter, counterAfter, cycleEnabled, enabled, ↓reduceIte]
    refine (read_plan reads rs .mcycle (by decide)).bind ?_
    refine (write_plan reads rs .mcycle (_root_.Sail.BitVec.addInt (rs .mcycle) 1) (by decide)).bind ?_
    apply time_dispatch_plan
    simpa [Sail.Registers.write] using env
  · simp only [cycleEnabled] at enabled
    simp only [clockAfter, counterAfter, cycleEnabled, enabled]
    change Returns reads rs _ () (JalLoop.clintAfter (timeAfter rs))
    exact time_dispatch_plan reads rs env

/-- Machine-mode global MIE disable suffices for every pending value and every
independent hardware-pin result. Neither interrupt-enable masks nor pending bits
are assumed zero. -/
theorem getPendingSet_plan (reads : ReadAllowed) (rs : RegisterFile)
    (status : rs .mstatus = 0xA00000000#64) :
    Returns reads rs (getPendingSet .Machine) none rs := by
  unfold getPendingSet
  refine ExecPlan.bind
    (readOnly_plan reads rs JalLoop.currentlyEnabled_s_readOnly) ?_
  intro enabled after same
  subst after
  cases enabled
  · refine (pure_plan reads rs (0#64)).bind ?_
    refine ExecPlan.bind
      (readOnly_plan reads rs (JalLoop.read_mip_readOnly .IncludePlatformInterrupts)) ?_
    intro pending after same
    subst after
    refine (read_plan reads rs .mie (by decide)).bind ?_
    refine (read_plan reads rs .mie (by decide)).bind ?_
    refine (read_plan reads rs .mstatus (by decide)).bind ?_
    refine (read_plan reads rs .mstatus (by decide)).bind ?_
    rw [status]
    exact pure_plan reads rs none
  · refine (read_plan reads rs .mideleg (by decide)).bind ?_
    refine ExecPlan.bind
      (readOnly_plan reads rs (JalLoop.read_mip_readOnly .IncludePlatformInterrupts)) ?_
    intro pending after same
    subst after
    refine (read_plan reads rs .mie (by decide)).bind ?_
    refine (read_plan reads rs .mie (by decide)).bind ?_
    refine (read_plan reads rs .mstatus (by decide)).bind ?_
    refine (read_plan reads rs .mstatus (by decide)).bind ?_
    rw [status]
    exact pure_plan reads rs none

theorem dispatchInterrupt_plan (reads : ReadAllowed) (rs : RegisterFile)
    (status : rs .mstatus = 0xA00000000#64) :
    Returns reads rs (dispatchInterrupt .Machine) none rs := by
  unfold dispatchInterrupt
  refine (getPendingSet_plan reads rs status).bind ?_
  exact pure_plan reads rs none

end MachCSL.Machine.JalLoopPlan
