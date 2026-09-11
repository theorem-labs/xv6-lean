import Xv6.Kernel.PushOffStackPure

namespace Xv6.Kernel.PushOffStack
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
theorem load_factor [Platform] (slot : Slot) : body .load slot = (do
    let sp ← rX_bits (.Regidx 2#5)
    KptMemory.program .load (sp + offset slot) 0#64 >>= loadTail slot) := by
  rw [load_body]
  unfold execute_LOAD
  rw [immediate_eq]
  change (pure () >>= fun _ => vmem_read (.Regidx 2#5) (offset slot) 8 (.Load .Data) false false false >>= _) = _
  rw [BootPmp.sail_pure_bind]
  unfold vmem_read get_transformed_data_addr ext_data_get_addr
    _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [liftM, ExceptT.bind, ExceptT.pure, Bind.bind, Pure.pure, Sail.ArchSem.FreeM.bind]
  change (Sail.ArchSem.FreeM.impure (Event.readReg .x2) _ : SailM ExecutionResult) = Sail.ArchSem.FreeM.impure (Event.readReg .x2) _
  congr 1
  funext sp
  change BitVec 64 at sp
  simp only [Pure.pure, Sail.ArchSem.FreeM.bind, regval_from_reg, Function.comp_def, free_assoc, ExceptT.bindCont]
  unfold KptMemory.program
  simp only [Bind.bind]
  conv =>
    rhs
    change Sail.ArchSem.FreeM.bind (Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + offset slot)) (.Load .Data)) (fun va => (vmem_read_addr va 8 (.Load .Data) false false false : SailM (KptMemory.Result .load)))) (loadTail slot)
    rw [free_assoc]
  apply congrArg (fun k : virtaddr → SailM ExecutionResult => Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + offset slot)) (.Load .Data)) k)
  funext va
  dsimp only [ExceptT.mk, ExceptT.run, Sail.ArchSem.FreeM.bind]
  generalize vmem_read_addr va 8 (.Load .Data) false false false = memory
  induction memory with
  | pure response =>
    cases response with
    | Ok word =>
      have extend : extend_value false word = word := by simp [extend_value, sign_extend, Sail.BitVec.signExtend]
      change (wX_bits (regidx slot) (extend_value false word) >>= fun _ => pure (.Retire_Success ())) = loadTail slot (.Ok word)
      rw [extend]
      rfl
    | Err error => rfl
  | impure e k ih =>
    change (Sail.ArchSem.FreeM.impure e _ : SailM ExecutionResult) = Sail.ArchSem.FreeM.impure e _
    congr 1
    funext x
    exact ih x


theorem virtual_write_factor [Platform] (offset new : BitVec 64) :
    vmem_write (.Regidx 2#5) offset 8 new (.Store .Data) false false false = (do
      let sp ← rX_bits (.Regidx 2#5)
      KptMemory.program .store (sp + offset) new) := by
  unfold vmem_write get_transformed_data_addr ext_data_get_addr
    _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [liftM, ExceptT.bind, ExceptT.pure, Bind.bind, Pure.pure, Sail.ArchSem.FreeM.bind]
  change (Sail.ArchSem.FreeM.impure (Event.readReg .x2) _ : SailM (KptMemory.Result .store)) = Sail.ArchSem.FreeM.impure (Event.readReg .x2) _
  congr 1
  funext sp
  change BitVec 64 at sp
  simp only [Pure.pure, Sail.ArchSem.FreeM.bind, regval_from_reg, Function.comp_def, free_assoc, ExceptT.bindCont]
  unfold KptMemory.program
  change Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + offset)) (.Store .Data)) _ = Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + offset)) (.Store .Data)) _
  apply congrArg (fun k : virtaddr → SailM (KptMemory.Result .store) => Sail.ArchSem.FreeM.bind (transform_effective_address (.Virtaddr (sp + offset)) (.Store .Data)) k)
  funext va
  dsimp only [ExceptT.mk, ExceptT.run, Sail.ArchSem.FreeM.bind]
  generalize vmem_write_addr va 8 new (.Store .Data) false false false = memory
  induction memory with
  | pure response => rfl
  | impure e k ih =>
    change (Sail.ArchSem.FreeM.impure e _ : SailM (KptMemory.Result .store)) = Sail.ArchSem.FreeM.impure e _
    congr 1
    funext x
    exact ih x

theorem store_factor [Platform] (slot : Slot) : body .store slot = (do
    let new ← rX_bits (regidx slot)
    let sp ← rX_bits (.Regidx 2#5)
    KptMemory.program .store (sp + offset slot) new >>= storeTail) := by
  rw [store_body]
  unfold execute_STORE
  rw [immediate_eq]
  change (pure () >>= fun _ => rX_bits (regidx slot) >>= fun new => pure (Sail.BitVec.extractLsb new 63 0) >>= fun new => vmem_write (.Regidx 2#5) (offset slot) 8 (BitVec.setWidth 64 new) (.Store .Data) false false false >>= storeTail) = _
  simp only [BootPmp.sail_pure_bind, SupervisorWrite.full_word, BitVec.setWidth_eq]
  apply congrArg (fun k : BitVec 64 → SailM ExecutionResult => rX_bits (regidx slot) >>= k)
  funext new
  rw [virtual_write_factor]
  exact BootPmp.sail_bind_assoc (rX_bits (.Regidx 2#5)) (fun sp => KptMemory.program .store (sp + offset slot) new) storeTail

theorem pureSpec [Platform] : PureSpec :=
  ⟨inventory, store_body, load_body, store_factor, load_factor, store_false, store_error,
    load_error, entry_after, map_other, after_sp, after_address, anchored,
    fun s slot => ⟨footprint_unique s slot, bare_footprint_unique s slot⟩,
    footprint_counts, footprint_members, ambient⟩

end Xv6.Kernel.PushOffStack
