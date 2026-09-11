import Xv6.Kernel.MycpuMemoryDefs
import MachCSL.Logic.SupervisorAddressPlan
import MachCSL.Logic.SupervisorBareReadPlan
import MachCSL.Logic.SupervisorBareWritePlan
import MachCSL.Logic.RegisterPlanProofs

namespace Xv6.Kernel.MycpuMemory
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 100000

private theorem returns_bind {fp : RegisterFootprint.Footprint} {rs middle final : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value middle)
    (rest : RegisterPlan.Returns fp middle (next value) result final) :
    RegisterPlan.Returns fp rs (program >>= next) result final :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest
private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩
private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih
private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact returns_bind plan (pure_plan fp rs _)

private theorem widen_read {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {req : MemoryReadWP.ReadRequest 8} {program : SailM α} {tail}
    (cut : SupervisorRead.Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : SupervisorRead.Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen first members) ih
private theorem widen_write {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {req : MemoryWriteWP.WriteRequest 8} {program : SailM α} {tail}
    (cut : SupervisorWrite.Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : SupervisorWrite.Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen first members) ih

theorem footprint_unique (slot : Slot) (shares : Shares) (dq : DFrac) :
    RegisterFootprint.Unique (footprint slot shares dq) := by
  cases slot <;> simp [RegisterFootprint.Unique, footprint, dataRegister,
    SupervisorBareFetch.footprint, SupervisorBare.footprint, SupervisorFetchRead.footprint]

theorem store_body_eq [Platform] (slot : Slot) :
    storeBody slot = execute_STORE (immediate slot) (dataIndex slot) (.Regidx 2#5) 8 := by
  cases slot <;> rfl

theorem load_body_eq [Platform] (slot : Slot) :
    loadBody slot = execute_LOAD (immediate slot) (.Regidx 2#5) (dataIndex slot) false 8 := by
  cases slot <;> rfl

theorem immediate_eq (slot : Slot) : sign_extend (m := 64) (immediate slot) = offset slot := by
  cases slot <;> rfl

theorem data_plan (slot : Slot) (shares : Shares) (rs : RegisterFile) :
    RegisterPlan.Returns (footprint slot shares shares.data) rs
      (rX_bits (dataIndex slot)) (dataValue slot rs) rs := by
  cases slot <;> exact .read (dq := shares.data) (by simp [footprint, dataRegister]) (.pure ⟨rfl, rfl⟩)

theorem address_plan (slot : Slot) (shares : Shares) (dq : DFrac) (rs : RegisterFile)
    (kind : SupervisorAddress.Kind) (config : SupervisorAddress.Config rs .Bare) :
    RegisterPlan.Returns (footprint slot shares dq) rs
      (get_transformed_data_addr (.Regidx 2#5) (offset slot) (SupervisorAddress.access kind) 8)
      (.Ext_DataAddr_OK (.Virtaddr (address slot rs))) rs := by
  have transform : RegisterPlan.Returns (footprint slot shares dq) rs
      (SupervisorAddress.program (address slot rs) kind) (.Virtaddr (address slot rs)) rs := by
    apply widen (SupervisorAddress.program_plan (addressShares shares) rs .Bare config _ kind)
    intro cell member
    simp only [SupervisorAddress.footprint, addressShares, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint]
  unfold get_transformed_data_addr ext_data_get_addr
  refine returns_bind (middle := rs) (value := .Ext_DataAddr_OK (.Virtaddr (address slot rs))) ?_ ?_
  · exact .read (dq := shares.sp) (by simp [footprint]) (.pure ⟨rfl, rfl⟩)
  · exact returns_bind transform (pure_plan _ _ _)

theorem virtual_read (slot : Slot) (shares : Shares) (rs : RegisterFile) (region : PMA_Region)
    (config : ReadConfig slot rs region) (aligned : TsoContextWord.Aligned (address slot rs)) :
    SupervisorRead.OneRead (footprint slot shares (.own 1)) rs (address slot rs)
      (vmem_read (.Regidx 2#5) (offset slot) 8 (.Load .Data) false false false)
      (fun word => .Ok word) := by
  obtain ⟨tail, cut, success, error⟩ := SupervisorBareRead.program_boundary shares.bare rs _ region config.memory aligned
  have read : SupervisorRead.OneRead (footprint slot shares (.own 1)) rs (address slot rs)
      (SupervisorBareRead.program (address slot rs)) (fun word => .Ok word) :=
    ⟨tail, widen_read cut (fun _ h => List.mem_append_right _ h), success, error⟩
  have first :=  address_plan slot shares (.own 1) rs .load config.transform
  unfold vmem_read _root_.Sail.SailME.run PreSail.PreSailME.run
  apply SupervisorRead.OneRead.bind (value := fun word => (Except.ok (.Ok word) : Except SupervisorBareRead.Result SupervisorBareRead.Result))
  · refine SupervisorRead.OneRead.prefix (value := (Except.ok (.Virtaddr (address slot rs)) : Except SupervisorBareRead.Result virtaddr)) ?_ ?_
    · exact returns_bind (lift_except first SupervisorBareRead.Result) (pure_plan _ _ _)
    · exact SupervisorRead.OneRead.bind read _ _ (fun _ => rfl)
  · intro word; rfl

theorem virtual_write [Platform] (slot : Slot) (shares : Shares) (rs : RegisterFile)
    (region : PMA_Region) (word : BitVec 64) (config : WriteConfig slot rs region)
    (aligned : TsoContextWord.Aligned (address slot rs)) :
    SupervisorWrite.OneWrite (footprint slot shares shares.data) rs (address slot rs) word
      (vmem_write (.Regidx 2#5) (offset slot) 8 word (.Store .Data) false false false)
      (fun value => .Ok value) := by
  obtain ⟨tail, cut, success, error⟩ := SupervisorBareWrite.virtual_boundary shares.bare rs _ word region config.memory aligned
  have write : SupervisorWrite.OneWrite (footprint slot shares shares.data) rs (address slot rs) word
      (SupervisorBareWrite.program (address slot rs) word) (fun value => .Ok value) :=
    ⟨tail, widen_write cut (fun _ h => List.mem_append_right _ h), success, error⟩
  have first :=  address_plan slot shares shares.data rs .store config.transform
  unfold vmem_write _root_.Sail.SailME.run PreSail.PreSailME.run
  apply SupervisorWrite.OneWrite.bind (value := fun b => (Except.ok (.Ok b) : Except SupervisorBareWrite.Result SupervisorBareWrite.Result))
  · refine SupervisorWrite.OneWrite.prefix (value := (Except.ok (.Virtaddr (address slot rs)) : Except SupervisorBareWrite.Result virtaddr)) ?_ ?_
    · exact returns_bind (lift_except first SupervisorBareWrite.Result) (pure_plan _ _ _)
    · exact SupervisorWrite.OneWrite.bind write _ _ (fun _ => rfl)
  · intro b; rfl

/-- The actual STORE body preserves the false-write tail as well as success. -/
theorem store_boundary [Platform] (slot : Slot) (shares : Shares) (rs : RegisterFile)
    (region : PMA_Region) (config : WriteConfig slot rs region)
    (aligned : TsoContextWord.Aligned (address slot rs)) :
    SupervisorWrite.OneWrite (footprint slot shares shares.data) rs (address slot rs) (dataValue slot rs)
      (storeBody slot) (fun _ => .Retire_Success ()) := by
  rw [store_body_eq]
  unfold execute_STORE
  rw [immediate_eq]
  apply SupervisorWrite.OneWrite.prefix (pure_plan (footprint slot shares shares.data) rs ())
  refine SupervisorWrite.OneWrite.prefix (value := dataValue slot rs) ?_ ?_
  · cases slot <;> apply RegisterPlan.Plan.read (dq := shares.data) (by simp [footprint, dataRegister])
    all_goals apply RegisterPlan.Plan.pure
    all_goals constructor
    all_goals first | rfl | simp only [SupervisorWrite.full_word, BitVec.setWidth_eq]
  · apply SupervisorWrite.OneWrite.prefix (pure_plan (footprint slot shares shares.data) rs _)
    have exactWrite := virtual_write slot shares rs region (dataValue slot rs) config aligned
    have finish := SupervisorWrite.OneWrite.bind exactWrite
      (fun result => match result with | .Ok _ => pure (.Retire_Success ()) | .Err e => pure e)
      (fun _ => .Retire_Success ()) (fun _ => rfl)
    have slice : BitVec.setWidth (8 * 8)
        (Sail.BitVec.extractLsb (dataValue slot rs) (((8 : Int) * 8) - 1).toNat 0) = dataValue slot rs := by
      change BitVec.setWidth 64 (Sail.BitVec.extractLsb (dataValue slot rs) 63 0) = _
      rw [SupervisorWrite.full_word, BitVec.setWidth_eq]
    exact Eq.mpr (congrArg (fun value : BitVec 64 =>
      SupervisorWrite.OneWrite (footprint slot shares shares.data) rs (address slot rs) (dataValue slot rs)
        (vmem_write (.Regidx 2#5) (offset slot) 8 value (.Store .Data) false false false >>=
          fun result => match result with | .Ok _ => pure (.Retire_Success ()) | .Err e => pure e)
        (fun _ => .Retire_Success ())) slice) finish

/-- Complete residual after every successful word/tag, plus the actual error exit.
The real destination write remains after the read boundary. -/
theorem load_boundary [Platform] (slot : Slot) (shares : Shares) (rs : RegisterFile)
    (region : PMA_Region) (config : ReadConfig slot rs region)
    (aligned : TsoContextWord.Aligned (address slot rs)) :
    ∃ tail, SupervisorRead.Boundary (footprint slot shares (.own 1)) rs
      (SupervisorRead.request (address slot rs)) (loadBody slot) tail ∧
      (∀ word tag, tail (.Ok (word, tag)) = loadTail slot word) ∧
      tail (.Err ()) = fail .Exit := by
  obtain ⟨tail, cut, success, error⟩ := virtual_read slot shares rs region config aligned
  rw [load_body_eq]
  unfold execute_LOAD
  rw [immediate_eq]
  refine ⟨_, .prefix (pure_plan (footprint slot shares (.own 1)) rs ()) (cut.bind _), ?_, ?_⟩
  · intro word tag
    rw [success, BootPmp.sail_pure_bind]
    have extend : extend_value false word = word := by
      simp [extend_value, sign_extend, Sail.BitVec.signExtend]
    simp only [extend]
    rfl
  · rw [error]
    change (Sail.ArchSem.FreeM.impure (.error Sail.Error.Exit) _ : SailM ExecutionResult) =
      Sail.ArchSem.FreeM.impure (.error Sail.Error.Exit) Empty.elim
    congr 1
    funext impossible
    exact Empty.elim impossible

theorem load_tail_plan (slot : Slot) (shares : Shares) (rs : RegisterFile) (word : BitVec 64) :
    RegisterPlan.Returns (footprint slot shares (.own 1)) rs (loadTail slot word)
      (.Retire_Success ()) (after slot rs word) := by
  cases slot <;> exact .write (by simp [footprint, dataRegister]) (.pure ⟨rfl, rfl⟩)

theorem after_value (slot : Slot) (rs : RegisterFile) (word : BitVec 64) :
    dataValue slot (after slot rs word) = word := by
  cases slot <;> simp [dataValue, after, MachCSL.Sail.Registers.write]
theorem after_sp (slot : Slot) (rs : RegisterFile) (word : BitVec 64) :
    after slot rs word .x2 = rs .x2 := by cases slot <;> simp [after, MachCSL.Sail.Registers.write]
theorem after_PC (slot : Slot) (rs : RegisterFile) (word : BitVec 64) :
    after slot rs word .PC = rs .PC := by cases slot <;> simp [after, MachCSL.Sail.Registers.write]
theorem after_nextPC (slot : Slot) (rs : RegisterFile) (word : BitVec 64) :
    after slot rs word .nextPC = rs .nextPC := by cases slot <;> simp [after, MachCSL.Sail.Registers.write]
theorem after_address (slot : Slot) (rs : RegisterFile) (word : BitVec 64) :
    address slot (after slot rs word) = address slot rs := by simp [address, after_sp]

/-- Source save slots after the actual modular sixteen-byte stack push. -/
theorem pushed_ra_address (rs : RegisterFile) (entrySP : BitVec 64) :
    address .ra (MachCSL.Sail.Registers.write rs .x2 (entrySP - 16#64)) = entrySP - 8#64 := by
  simp [address, offset, BitVec.sub_eq_add_neg, BitVec.add_assoc]
theorem pushed_s0_address (rs : RegisterFile) (entrySP : BitVec 64) :
    address .s0 (MachCSL.Sail.Registers.write rs .x2 (entrySP - 16#64)) = entrySP - 16#64 := by
  simp [address, offset]

end Xv6.Kernel.MycpuMemory
