import Xv6.Kernel.PushOffWord4Pure
import Xv6.Kernel.KptMemory4Plan

namespace Xv6.Kernel.PushOffWord4
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem free_assoc {α β γ : Type} (m : SailM α) (f : α → SailM β) (g : β → SailM γ) :
    Sail.ArchSem.FreeM.bind (Sail.ArchSem.FreeM.bind m f) g =
    Sail.ArchSem.FreeM.bind m (fun x => Sail.ArchSem.FreeM.bind (f x) g) :=
  BootPmp.sail_bind_assoc m f g

/-- Full generated load wrapper, including every memory error arm and the
actual destination register write after the ordinary read. -/
theorem load_factor [Platform] (imm : BitVec 12) : execute_LOAD imm (.Regidx 10#5) (.Regidx 15#5) false 4 = (do
    let sp ← rX_bits (.Regidx 10#5)
    KptMemory4.program .load (sp + imm.signExtend 64) 0#32 >>= loadTail) := by
  unfold execute_LOAD
  change (pure () >>= fun _ => vmem_read (.Regidx 10#5) (imm.signExtend 64) 4 (.Load .Data) false false false >>= _) = _
  rw [BootPmp.sail_pure_bind]
  unfold vmem_read get_transformed_data_addr ext_data_get_addr
    _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [liftM, ExceptT.bind, ExceptT.pure, Bind.bind, Pure.pure, Sail.ArchSem.FreeM.bind]
  change (Sail.ArchSem.FreeM.impure (Event.readReg .x10) _ : SailM ExecutionResult) = Sail.ArchSem.FreeM.impure (Event.readReg .x10) _
  congr 1
  funext sp
  change BitVec 64 at sp
  simp only [Pure.pure, Sail.ArchSem.FreeM.bind, regval_from_reg, Function.comp_def, free_assoc, ExceptT.bindCont]
  unfold KptMemory4.program
  simp only [Bind.bind]
  conv =>
    rhs
    change Sail.ArchSem.FreeM.bind (Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + imm.signExtend 64)) (.Load .Data)) (fun va => (vmem_read_addr va 4 (.Load .Data) false false false : SailM (KptMemory4.Result .load)))) (loadTail)
    rw [free_assoc]
  apply congrArg (fun k : virtaddr → SailM ExecutionResult => Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + imm.signExtend 64)) (.Load .Data)) k)
  funext va
  dsimp only [ExceptT.mk, ExceptT.run, Sail.ArchSem.FreeM.bind]
  generalize vmem_read_addr va 4 (.Load .Data) false false false = memory
  induction memory with
  | pure response =>
    cases response with
    | Ok word =>
      have extend : extend_value false word = word.signExtend 64 := rfl
      change (wX_bits ((.Regidx 15#5)) (extend_value false word) >>= fun _ => pure (.Retire_Success ())) = loadTail (.Ok word)
      rw [extend]
      rfl
    | Err error => rfl
  | impure e k ih =>
    change (Sail.ArchSem.FreeM.impure e _ : SailM ExecutionResult) = Sail.ArchSem.FreeM.impure e _
    congr 1
    funext x
    exact ih x


theorem virtual_write_factor [Platform] (offset : BitVec 64) (new : BitVec 32) :
    vmem_write (.Regidx 10#5) offset 4 new (.Store .Data) false false false = (do
      let sp ← rX_bits (.Regidx 10#5)
      KptMemory4.program .store (sp + offset) new) := by
  unfold vmem_write get_transformed_data_addr ext_data_get_addr
    _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [liftM, ExceptT.bind, ExceptT.pure, Bind.bind, Pure.pure, Sail.ArchSem.FreeM.bind]
  change (Sail.ArchSem.FreeM.impure (Event.readReg .x10) _ : SailM (KptMemory4.Result .store)) = Sail.ArchSem.FreeM.impure (Event.readReg .x10) _
  congr 1
  funext sp
  change BitVec 64 at sp
  simp only [Pure.pure, Sail.ArchSem.FreeM.bind, regval_from_reg, Function.comp_def, free_assoc, ExceptT.bindCont]
  unfold KptMemory4.program
  change Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + offset)) (.Store .Data)) _ = Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + offset)) (.Store .Data)) _
  apply congrArg (fun k : virtaddr → SailM (KptMemory4.Result .store) => Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + offset)) (.Store .Data)) k)
  funext va
  dsimp only [ExceptT.mk, ExceptT.run, Sail.ArchSem.FreeM.bind]
  generalize vmem_write_addr va 4 new (.Store .Data) false false false = memory
  induction memory with
  | pure response => rfl
  | impure e k ih =>
    change (Sail.ArchSem.FreeM.impure e _ : SailM (KptMemory4.Result .store)) = Sail.ArchSem.FreeM.impure e _
    congr 1
    funext x
    exact ih x

theorem store_factor [Platform] (imm : BitVec 12) :
    execute_STORE imm (.Regidx 15#5) (.Regidx 10#5) 4 = (do
      let new ← rX_bits (.Regidx 15#5)
      let base ← rX_bits (.Regidx 10#5)
      KptMemory4.program .store (base + imm.signExtend 64) (new.setWidth 32) >>= storeTail) := by
  unfold execute_STORE
  change (pure () >>= fun _ => rX_bits (.Regidx 15#5) >>= fun new => pure (Sail.BitVec.extractLsb new 31 0) >>= fun new => vmem_write (.Regidx 10#5) (imm.signExtend 64) 4 new (.Store .Data) false false false >>= storeTail) = _
  rw [BootPmp.sail_pure_bind]
  apply congrArg (fun k : BitVec 64 → SailM ExecutionResult => rX_bits (.Regidx 15#5) >>= k)
  funext new
  rw [BootPmp.sail_pure_bind]
  have low : Sail.BitVec.extractLsb new 31 0 = new.setWidth 32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  rw [low, virtual_write_factor]
  exact BootPmp.sail_bind_assoc (rX_bits (.Regidx 10#5))
    (fun base => KptMemory4.program .store (base + imm.signExtend 64) (new.setWidth 32)) storeTail

theorem factor [Platform] (op : Op) : body op = factored op := by
  cases op
  case loadFirst => exact load_factor 120#12
  case loadAgain => exact load_factor 120#12
  case storeNoff => exact store_factor 120#12
  case storeIntena => exact store_factor 124#12

theorem nativePureSpec [Platform] : PureSpec :=
  ⟨factor, normalized, compressed, store_false, store_error, load_error, footprint_unique,
    footprint_counts, footprint_members, kpt_ambient, bare_config, map_other, after_address, after_sp⟩
end Xv6.Kernel.PushOffWord4
