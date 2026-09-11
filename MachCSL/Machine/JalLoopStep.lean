import MachCSL.Machine.JalLoopActive

/-! Actual generated retirement postlude, including modular minstret updates. -/
namespace MachCSL.Machine.JalLoop
open LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

def enableIncrement (d : Dynamic) : Dynamic := { d with increment := true }

private theorem enable_override (base : RegisterFile) (d : Dynamic) :
    Sail.Registers.write (override base d) .minstret_increment true =
      override base (enableIncrement d) := by
  funext r
  cases r <;> rfl

theorem enable_registers (cpu : CPU) (d : Dynamic) :
    Sail.Registers.write (registers cpu d) .minstret_increment true =
      registers cpu (enableIncrement d) := enable_override _ d

private theorem retire_override (base : RegisterFile) (d : Dynamic) :
    Sail.Registers.write (override base (enableIncrement d)) .minstret
      (_root_.Sail.BitVec.addInt d.retired 1) = override base (retire d) := by
  funext r
  cases r <;> rfl

theorem retire_registers (cpu : CPU) (d : Dynamic) :
    Sail.Registers.write (registers cpu (enableIncrement d)) .minstret
      (_root_.Sail.BitVec.addInt d.retired 1) = registers cpu (retire d) := retire_override _ d

theorem tick_pc_exec (rs : RegisterFile) (pc : rs .nextPC = rs .PC) :
    RegisterExec (tick_pc ()) rs () rs := by
  unfold tick_pc
  refine (registerExec_read rs .nextPC).bind ?_
  have write : Sail.Registers.write rs .PC (rs .nextPC) = rs := by
    rw [pc, Sail.Registers.write_current]
  have h := registerExec_write rs .PC (rs .nextPC)
  rw [write] at h
  refine h.bind ?_
  refine (registerExec_read rs .PC).bind ?_
  exact (registerExec_pure () rs rs).mpr rfl

theorem try_step_fromFetch [Platform] (cpu : CPU) (d : Dynamic)
    (fetched : FetchExec (loadedRam jalImage) (fetch ()) (registers cpu (enableIncrement d))
      (.F_Base 0x6f#32) (registers cpu (enableIncrement d))) :
    FetchExec (loadedRam jalImage) (try_step 0 false) (registers cpu d)
      false (registers cpu (retire d)) := by
  have h := boot_static (BitVec.ofNat 64 cpu.val)
  simp only [Prod.mk.injEq] at h
  unfold try_step
  refine ((registerExec_read (registers cpu d) .cur_privilege).fetchExec _).bind ?_
  rw [show registers cpu d .cur_privilege = .Machine from h.2.2.2.2.2.2.2.1]
  refine ((should_inc_minstret_exec (registers cpu d) h.2.2.2.1 h.2.2.2.2.2.1).fetchExec _).bind ?_
  have enable := registerExec_write (registers cpu d) .minstret_increment true
  rw [enable_registers] at enable
  refine (enable.fetchExec _).bind ?_
  let rs := registers cpu (enableIncrement d)
  have active : rs .hart_state = .HART_ACTIVE () := h.2.2.2.2.2.2.2.2
  refine ((registerExec_read rs .hart_state).fetchExec _).bind ?_
  rw [active]
  refine (run_hart_active_fromFetch cpu (enableIncrement d) fetched).bind ?_
  refine ((registerExec_read rs .hart_state).fetchExec _).bind ?_
  rw [active]
  refine ((registerExec_read rs .hart_state).fetchExec _).bind ?_
  rw [active]
  have pc : rs .nextPC = rs .PC := by
    exact (bootRegisters_pc _ _).2.trans (bootRegisters_pc _ _).1.symm
  refine ((tick_pc_exec rs pc).fetchExec _).bind ?_
  refine ((registerExec_read rs .minstret_increment).fetchExec _).bind ?_
  change FetchExec _ (do
    PreSail.writeReg .minstret (_root_.Sail.BitVec.addInt (← PreSail.readReg .minstret) 1)
    pure false) rs false (registers cpu (retire d))
  refine ((registerExec_read rs .minstret).fetchExec _).bind ?_
  have retired := registerExec_write rs .minstret (_root_.Sail.BitVec.addInt d.retired 1)
  rw [retire_registers] at retired
  refine (retired.fetchExec _).bind ?_
  exact ((registerExec_pure _ _ _).mpr rfl).fetchExec _

end MachCSL.Machine.JalLoop
