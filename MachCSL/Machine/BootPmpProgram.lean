import MachCSL.Machine.BootPmpDefs

/-! Proof-only factorization of the actual generated boot chain at reset_pmp.
The equality theorem checks this split against the generated program. -/
namespace MachCSL.Machine.BootPmp
open LeanPaperStock.Functions
open _root_.Sail

def beforePmp (vector hart : BitVec 64) : SailM Unit := do
  boardWired vector hart
  boardRegisters pmaBoot
  assert (← config_is_valid ()) "Default config is invalid."
  writeReg Register.hart_state (.HART_ACTIVE ())
  writeReg Register.cur_privilege .Machine
  writeReg Register.mstatus (Sail.BitVec.updateSubrange (← readReg Register.mstatus) 3 3 0#1)
  writeReg Register.mstatus (Sail.BitVec.updateSubrange (← readReg Register.mstatus) 17 17 0#1)
  (reset_tvecs ())
  (long_csr_write_callback "mstatus" "mstatush" (← readReg Register.mstatus))
  (reset_misa ())
  (cancel_reservation ())
  writeReg Register.PC (← readReg Register.pc_reset_address)
  writeReg Register.nextPC (← readReg Register.pc_reset_address)
  writeReg Register.mcause (zeros (n := 64))
  (csr_name_write_callback "mcause" (← readReg Register.mcause))

def afterPmp : SailM Unit := do
  writeReg Register.mseccfg (Sail.BitVec.updateSubrange (← readReg Register.mseccfg) 9 9
    (bool_to_bit (false : Bool)))
  writeReg Register.mseccfg (Sail.BitVec.updateSubrange (← readReg Register.mseccfg) 8 8
    (bool_to_bit (false : Bool)))
  if ((hartSupports .Ext_Zicfilp) : Bool)
  then writeReg Register.mseccfg (Sail.BitVec.updateSubrange (← readReg Register.mseccfg) 10 10 0#1)
  else (pure ())
  (reset_stateen ())
  writeReg Register.vstart (zeros (n := 64))
  writeReg Register.vl (zeros (n := 64))
  writeReg Register.vcsr (Sail.BitVec.updateSubrange (← readReg Register.vcsr) 2 1 0b00#2)
  writeReg Register.vcsr (Sail.BitVec.updateSubrange (← readReg Register.vcsr) 0 0 0#1)
  writeReg Register.vtype (Sail.BitVec.updateSubrange (← readReg Register.vtype) (64 -i 1) (64 -i 1) 1#1)
  writeReg Register.vtype (Sail.BitVec.updateSubrange (← readReg Register.vtype) (64 -i 2) 8
    (zeros (n := (64 -i 9))))
  writeReg Register.vtype (Sail.BitVec.updateSubrange (← readReg Register.vtype) 7 7 0#1)
  writeReg Register.vtype (Sail.BitVec.updateSubrange (← readReg Register.vtype) 6 6 0#1)
  writeReg Register.vtype (Sail.BitVec.updateSubrange (← readReg Register.vtype) 5 3 0b000#3)
  writeReg Register.vtype (Sail.BitVec.updateSubrange (← readReg Register.vtype) 2 0 0b000#3)
  reset_vmem ()
  reset_elp ()
  let _ := ext_reset ()
  init_boot_requirements ()

theorem sail_bind_assoc (m : SailM α) (f : α → SailM β) (g : β → SailM γ) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := by
  induction m with
  | pure x => rfl
  | impure e k ih =>
    apply congrArg (_root_.Sail.ArchSem.FreeM.impure e)
    funext x
    exact ih x

theorem sail_pure_bind (x : α) (f : α → SailM β) : ((pure x : SailM α) >>= f) = f x := rfl

theorem sail_ite_bind (p : Prop) [Decidable p] (a b : SailM α) (f : α → SailM β) :
    ((if p then a else b) >>= f) = if p then a >>= f else b >>= f := by
  split <;> rfl

theorem program_eq (vector hart : BitVec 64) :
    bootProgram vector hart pmaBoot =
      beforePmp vector hart >>= fun _ => reset_pmp () >>= fun _ => afterPmp := by
  unfold bootProgram beforePmp afterPmp init_model reset reset_sys
  simp only [sail_bind_assoc, sail_pure_bind, sail_ite_bind]
  rfl
end MachCSL.Machine.BootPmp
