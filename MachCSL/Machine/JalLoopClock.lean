import MachCSL.Machine.JalLoopReadOnly
import MachCSL.Machine.JalLoopBootFacts

/-! Compositional proofs for the actual generated counter and clock helpers. -/
namespace MachCSL.Machine.JalLoop
open LeanPaperStock.Functions

theorem should_inc_mcycle_exec (rs : RegisterFile)
    (inhibit : rs .mcountinhibit = 0#32) (config : rs .mcyclecfg = 0#64) :
    RegisterExec (should_inc_mcycle .Machine) rs true rs := by
  unfold should_inc_mcycle
  refine (registerExec_read rs .mcountinhibit).bind ?_
  refine (registerExec_read rs .mcyclecfg).bind ?_
  rw [inhibit, config]
  exact (registerExec_pure true rs rs).mpr rfl

theorem should_inc_minstret_exec (rs : RegisterFile)
    (inhibit : rs .mcountinhibit = 0#32) (config : rs .minstretcfg = 0#64) :
    RegisterExec (should_inc_minstret .Machine) rs true rs := by
  unfold should_inc_minstret
  refine (registerExec_read rs .mcountinhibit).bind ?_
  refine (registerExec_read rs .minstretcfg).bind ?_
  rw [inhibit, config]
  exact (registerExec_pure true rs rs).mpr rfl

def timerPending (rs : RegisterFile) : BitVec 64 :=
  _root_.Sail.BitVec.updateSubrange (rs .mip) 7 7
    (bool_to_bit (zopz0zIzJ_u (rs .mtimecmp) (rs .mtime)))

def clintAfter (rs : RegisterFile) : RegisterFile :=
  Sail.Registers.write rs .mip (timerPending rs)

private theorem sstc_pure : currentlyEnabled .Ext_Sstc = pure (hartSupports .Ext_Sstc) := by
  unfold currentlyEnabled
  rfl

theorem clint_dispatch_exec (rs : RegisterFile) (env : rs .menvcfg = 0#64) :
    RegisterExec (clint_dispatch false) rs () (clintAfter rs) := by
  unfold clint_dispatch
  refine (registerExec_read rs .mip).bind ?_
  refine (registerExec_read rs .mip).bind ?_
  refine (registerExec_read rs .mtimecmp).bind ?_
  refine (registerExec_read rs .mtime).bind ?_
  refine (registerExec_write rs .mip (timerPending rs)).bind ?_
  rw [sstc_pure]
  refine (registerExec_read (clintAfter rs) .menvcfg).bind ?_
  have env' : clintAfter rs .menvcfg = 0#64 := by
    simpa [clintAfter, Sail.Registers.write] using env
  rw [env']
  simp only [show (_get_MEnvcfg_STCE 0#64 == 1#1) = false by decide,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    show get_config_print_clint () = false from rfl]
  refine (registerExec_read (clintAfter rs) .mip).bind ?_
  simp only [Bool.or_false]
  change RegisterExec (if (rs .mip != clintAfter rs .mip) then
    (do
      let value ← read_mip .IncludePlatformInterrupts
      csr_name_write_callback "mip" value)
    else pure ()) (clintAfter rs) () (clintAfter rs)
  split
  · exact mip_read_callback_exec _
  · exact (registerExec_pure () _ _).mpr rfl

def clockAfter (rs : RegisterFile) : RegisterFile :=
  let rs := Sail.Registers.write rs .mcycle (_root_.Sail.BitVec.addInt (rs .mcycle) 1)
  let rs := Sail.Registers.write rs .mtime (_root_.Sail.BitVec.addInt (rs .mtime) 1)
  clintAfter rs

/-- Exact actual clock execution, with symbolic modulo counters and both
changed-mip callback cases. No guard on overflow or timer comparison is assumed. -/
theorem tick_clock_exec (rs : RegisterFile) (priv : rs .cur_privilege = .Machine)
    (inhibit : rs .mcountinhibit = 0#32) (config : rs .mcyclecfg = 0#64)
    (env : rs .menvcfg = 0#64) :
    RegisterExec (tick_clock ()) rs () (clockAfter rs) := by
  unfold tick_clock
  refine (registerExec_read rs .cur_privilege).bind ?_
  rw [priv]
  refine (should_inc_mcycle_exec rs inhibit config).bind ?_
  refine (registerExec_read rs .mcycle).bind ?_
  let afterCycle := Sail.Registers.write rs .mcycle (_root_.Sail.BitVec.addInt (rs .mcycle) 1)
  refine (registerExec_write rs .mcycle (_root_.Sail.BitVec.addInt (rs .mcycle) 1)).bind ?_
  refine (registerExec_read afterCycle .mtime).bind ?_
  let afterTime := Sail.Registers.write afterCycle .mtime
    (_root_.Sail.BitVec.addInt (afterCycle .mtime) 1)
  refine (registerExec_write afterCycle .mtime
    (_root_.Sail.BitVec.addInt (afterCycle .mtime) 1)).bind ?_
  apply clint_dispatch_exec afterTime
  simpa [afterTime, afterCycle, Sail.Registers.write] using env

theorem clockAfter_override (base : RegisterFile) (d : Dynamic) :
    clockAfter (override base d) = override base (clock d) := by
  funext r
  cases r <;> rfl

theorem clockAfter_registers (cpu : CPU) (d : Dynamic) :
    clockAfter (registers cpu d) = registers cpu (clock d) := clockAfter_override _ d

theorem tick_clock_registers (cpu : CPU) (d : Dynamic) :
    RegisterExec (tick_clock ()) (registers cpu d) () (registers cpu (clock d)) := by
  rw [← clockAfter_registers]
  have h := boot_static (BitVec.ofNat 64 cpu.val)
  simp only [Prod.mk.injEq] at h
  apply tick_clock_exec
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1

/-- Every register event, including all callback reads, is retained as a real
node step. Shared memory, devices, log, view and reservation are unchanged. -/
theorem tick_clock_nodeSteps [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent) (image : Memory.ByteMap 64)
    (state : LocalState Device) (cpu : CPU) (d : Dynamic)
    (canonical : state.registers = registers cpu d) :
    NodeSteps bus others hart image (tick_clock ()) state (.pure ())
      { state with registers := registers cpu (clock d) } := by
  apply registerExec_nodeSteps
  rw [canonical]
  exact tick_clock_registers cpu d

end MachCSL.Machine.JalLoop
