import MachCSL.Logic.RegisterPlanDefs

/-! Proof-facing factors of the actual generated `try_step`. Every original
postlude arm is retained; `FactorProofs` checks the complete factorization. -/
namespace MachCSL.Logic.SupervisorRetirement
open MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail _root_.Sail.ConcurrencyInterfaceV1
open _root_.PreSail _root_.Sail.ConcurrencyInterfaceV1.Free
open Register Step ExecutionResult HartState ExceptionType

variable [Platform]

def setup : SailM Unit := do
  let _ : Unit := ext_pre_step_hook ()
  writeReg minstret_increment (← should_inc_minstret (← readReg cur_privilege))

/-- The complete original postlude, including unsuccessful and waiting arms. -/
def postlude (step_val : _root_.Step) : SailM Bool := do
  match step_val with
  | .Step_Pending_Interrupt (intr, priv) =>
    (do
      let _ : Unit :=
        if ((get_config_print_instr ()) : Bool)
        then (print_bits "Handling interrupt: " (interruptType_bits_forwards intr))
        else ()
      (handle_interrupt intr priv))
  | .Step_Ext_Fetch_Failure e => (pure (ext_handle_fetch_check_error e))
  | .Step_Fetch_Failure (vaddr, e) => (handle_exception (bits_of_virtaddr vaddr) e)
  | .Step_Waiting _ =>
    assert (hart_is_waiting (← readReg hart_state)) "cannot be Waiting in a non-Wait state"
  | .Step_Execute (.Retire_Success (), _) =>
    assert (hart_is_active (← readReg hart_state)) "postlude/step.sail:219.74-219.75"
  | .Step_Execute (.ExecuteAs _, _) =>
    (internal_error "postlude/step.sail" 223
      "Multiple chained ExecuteAs (only one redirection is supported).")
  | .Step_Execute (.Trap (priv, exc, pc), _) => (set_next_pc (← (exception_handler priv exc pc)))
  | .Step_Execute (.Illegal_Instruction (), instbits) =>
    (handle_exception (zero_extend (m := 64) instbits) (E_Illegal_Instr ()))
  | .Step_Execute (.Virtual_Instruction (), instbits) =>
    (handle_exception (zero_extend (m := 64) instbits) (E_Virtual_Instr ()))
  | .Step_Execute (.Enter_Wait wr, instbits) =>
    (do
      if ((wait_is_nop wr) : Bool)
      then assert (hart_is_active (← readReg hart_state)) "postlude/step.sail:232.41-232.42"
      else
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "entering "
                  (HAppend.hAppend (wait_name_forwards wr)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_WAITING (wr, instbits))))
  | .Step_Execute (.Ext_CSR_Check_Failure (), _) => (pure (ext_check_CSR_fail ()))
  | .Step_Execute (.Ext_ControlAddr_Check_Failure e, _) => (pure (ext_handle_control_check_error e))
  | .Step_Execute (.Ext_DataAddr_Check_Failure e, _) => (pure (ext_handle_data_check_error e))
  | .Step_Execute (.Ext_XRET_Priv_Failure (), _) => (pure (ext_fail_xret_priv ()))
  match (← readReg hart_state) with
  | .HART_WAITING _ => (pure true)
  | .HART_ACTIVE () =>
    (do
      (tick_pc ())
      let retired : Bool :=
        match step_val with
        | .Step_Execute (.Retire_Success (), _) => true
        | .Step_Execute (.Enter_Wait wr, _) =>
          (if ((wait_is_nop wr) : Bool)
          then true
          else false)
        | _ => false
      if ((retired && (← readReg minstret_increment)) : Bool)
      then writeReg minstret (BitVec.addInt (← readReg minstret) 1)
      else (pure ())
      if ((get_config_rvfi ()) : Bool)
      then
        writeReg rvfi_pc_data (Sail.BitVec.updateSubrange (← readReg rvfi_pc_data) 127 64
          (zero_extend (m := 64) (← (get_arch_pc ()))))
      else (pure ())
      let _ : Unit := (ext_post_step_hook ())
      let _ : Unit :=
        if (retired : Bool)
        then (instret_callback ())
        else ()
      (pure false))

end MachCSL.Logic.SupervisorRetirement
