import MachCSL.Machine.JalLoopInstruction
import MachCSL.Machine.JalLoopDispatch
import MachCSL.Machine.JalLoopClock

/-! Composition of actual interrupt dispatch, fetch, decode and JAL execution. -/
namespace MachCSL.Machine.JalLoop
open LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

def activeAfter (rs : RegisterFile) : RegisterFile :=
  Sail.Registers.write (Sail.Registers.write rs .nextPC
    (_root_.Sail.BitVec.addInt (rs .PC) 4)) .nextPC jalImage.vector

theorem run_hart_active_exec [Platform] (cpu : CPU) (d : Dynamic)
    (fetched : FetchExec (loadedRam jalImage) (fetch ()) (registers cpu d)
      (.F_Base 0x6f#32) (registers cpu d)) :
    FetchExec (loadedRam jalImage) (run_hart_active 0) (registers cpu d)
      (.Step_Execute (.Retire_Success (), 0x6f#32)) (activeAfter (registers cpu d)) := by
  unfold run_hart_active _root_.Sail.SailME.run PreSail.PreSailME.run
  apply (fetchExec_bind _ _ _ _ _ _).mpr
  refine ⟨Except.ok (.Step_Execute (.Retire_Success (), 0x6f#32)),
    activeAfter (registers cpu d), ?_, ?_⟩
  · refine ((registerExec_read (registers cpu d) .cur_privilege).fetchExec _).bind ?_
    have h := boot_static (BitVec.ofNat 64 cpu.val)
    simp only [Prod.mk.injEq] at h
    change FetchExec _ (_ >>= _) _ _ _
    rw [show registers cpu d .cur_privilege = .Machine from h.2.2.2.2.2.2.2.1]
    refine (((registerRun_exec _ _ _ _ _ (dispatch_registers cpu d)).fetchExec _).liftExcept Step).bind ?_
    refine (fetched.liftExcept Step).bind ?_
    refine ((decode_registers cpu d).liftExcept Step).bind ?_
    simp only [show get_config_print_instr () = false from rfl, Bool.false_eq_true, ↓reduceIte]
    unfold is_landing_pad_expected
    refine ((registerExec_read (registers cpu d) .elp).fetchExec _).bind ?_
    rw [show registers cpu d .elp = 0#1 from (boot_instruction_static _).2]
    simp only [show (0#1 == landing_pad_bits_backwards .LP_EXPECTED) = false by decide,
]
    refine ((registerExec_read (registers cpu d) .PC).fetchExec _).bind ?_
    refine ((registerExec_write (registers cpu d) .nextPC
      (_root_.Sail.BitVec.addInt (registers cpu d .PC) 4)).fetchExec _).bind ?_
    let rs := Sail.Registers.write (registers cpu d) .nextPC
      (_root_.Sail.BitVec.addInt (registers cpu d .PC) 4)
    have pc : rs .PC = jalImage.vector := (bootRegisters_pc _ _).1
    have misa : rs .misa = 0x800000000014112d#64 := bootRegisters_misa _ _
    simp only [ExceptT.bindCont]
    apply FetchExec.exceptBind (a := .Retire_Success ())
    · apply FetchExec.exceptBind
        (((execute_JAL_exec rs pc misa).fetchExec _).liftExcept Step)
      exact ((registerExec_pure _ _ _).mpr rfl).fetchExec _
    · exact ((registerExec_pure _ _ _).mpr rfl).fetchExec _
  · exact ((registerExec_pure _ _ _).mpr rfl).fetchExec _

theorem activeAfter_registers (cpu : CPU) (d : Dynamic) :
    activeAfter (registers cpu d) = registers cpu d := by
  unfold activeAfter
  rw [Sail.Registers.write_overwrite]
  have h : registers cpu d .nextPC = jalImage.vector := (bootRegisters_pc _ _).2
  rw [← h, Sail.Registers.write_current]

theorem run_hart_active_fromFetch [Platform] (cpu : CPU) (d : Dynamic)
    (fetched : FetchExec (loadedRam jalImage) (fetch ()) (registers cpu d)
      (.F_Base 0x6f#32) (registers cpu d)) :
    FetchExec (loadedRam jalImage) (run_hart_active 0) (registers cpu d)
      (.Step_Execute (.Retire_Success (), 0x6f#32)) (registers cpu d) := by
  simpa only [activeAfter_registers] using run_hart_active_exec cpu d fetched

end MachCSL.Machine.JalLoop
