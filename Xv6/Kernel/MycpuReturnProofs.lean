import Xv6.Kernel.MycpuReturnDefs
import MachCSL.Logic.RegisterPlanProofs
import MachCSL.Machine.BootPmpProgram

namespace Xv6.Kernel.MycpuReturn
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem retPC_aligned (ra : BitVec 64) : _root_.Sail.BitVec.access (retPC ra) 0 = 0#1 := by
  simp [retPC, _root_.Sail.BitVec.update, _root_.Sail.BitVec.updateSubrange',
    _root_.Sail.BitVec.access]

theorem retPC_jalr (ra : BitVec 64) :
    _root_.Sail.BitVec.update (ra + sign_extend (m := 64) 0#12) 0 0#1 = retPC ra := by
  simp [sign_extend, _root_.Sail.BitVec.signExtend, retPC]

theorem source_config (rs : RegisterFile) (source : SourceConfig rs) : Config rs := by
  refine ⟨source.privilege, ?_, ?_⟩
  · rw [source.menvcfg]; rfl
  · rw [source.misa]; rfl

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint]
theorem pcFootprint_unique (shares : Shares) (pcShare : DFrac) :
    RegisterFootprint.Unique (pcFootprint shares pcShare) := by
  simp [RegisterFootprint.Unique, pcFootprint, footprint]

theorem after_nextPC (rs : RegisterFile) : after rs .nextPC = retPC (rs .x1) := by simp [after]
theorem after_other (rs : RegisterFile) (r : Register) (different : r ≠ .nextPC) :
    after rs r = rs r := by simp [after, MachCSL.Sail.Registers.write, Ne.symm different]
theorem after_PC (rs : RegisterFile) : after rs .PC = rs .PC := after_other rs _ (by decide)

private theorem returns_bind {fp : RegisterFootprint.Footprint} {rs middle after : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value middle)
    (rest : RegisterPlan.Returns fp middle (next value) result after) :
    RegisterPlan.Returns fp rs (program >>= next) result after :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩
private theorem read_plan (shares : Shares) (rs : RegisterFile) (r : Register)
    (dq : DFrac) (member : (r, dq) ∈ footprint shares) :
    RegisterPlan.Returns (footprint shares) rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl, rfl⟩)

theorem elp_plan (shares : Shares) (rs : RegisterFile) (config : Config rs) :
    RegisterPlan.Returns (footprint shares) rs (update_elp_state (.Regidx 1#5)) () rs := by
  unfold update_elp_state
  have enabled : RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_Zicfilp) false rs := by
    unfold currentlyEnabled
    rw [show currentlyEnabled .Ext_Zicsr = (pure true : SailM Bool) by
      unfold currentlyEnabled
      rw [show hartSupports .Ext_Zicsr = true by unfold hartSupports; rfl]]
    simp only [BootPmp.sail_pure_bind]
    refine returns_bind (read_plan shares rs .cur_privilege shares.privilege (by simp [footprint])) ?_
    rw [config.privilege]
    have inner : RegisterPlan.Returns (footprint shares) rs (get_xLPE .Supervisor) false rs := by
      unfold get_xLPE
      refine returns_bind (read_plan shares rs .menvcfg shares.menvcfg (by simp [footprint])) ?_
      rw [config.lpe]
      exact pure_plan _ _ _
    refine returns_bind inner ?_
    rw [show hartSupports .Ext_Zicfilp = true by unfold hartSupports; rfl]
    exact pure_plan _ _ _
  exact returns_bind enabled (pure_plan _ _ _)

theorem zca_plan (shares : Shares) (rs : RegisterFile) (config : Config rs) :
    RegisterPlan.Returns (footprint shares) rs (currentlyEnabled .Ext_Zca) true rs := by
  have inner : RegisterPlan.Returns (footprint shares) rs
      (currentlyEnabled .Ext_C) true rs := by
    unfold currentlyEnabled
    refine returns_bind (read_plan shares rs .misa shares.misa (by simp [footprint])) ?_
    rw [config.compressed, show hartSupports .Ext_C = true by simp [hartSupports, LeanPaperStock.Functions.not, LeanPaperStock.Functions.xlen]]
    exact pure_plan _ _ _
  unfold currentlyEnabled
  refine returns_bind inner ?_
  rw [show hartSupports .Ext_Zca = true by unfold hartSupports; rfl,
    show hartSupports .Ext_C = true by simp [hartSupports, LeanPaperStock.Functions.not, LeanPaperStock.Functions.xlen]]
  exact pure_plan _ _ _

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs middle : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value middle) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) middle := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) middle
  exact returns_bind plan (pure_plan fp middle _)

theorem jump_plan (shares : Shares) (rs : RegisterFile) (config : Config rs) (ra : BitVec 64) :
    RegisterPlan.Returns (footprint shares) rs (jump_to (retPC ra)) (.Retire_Success ())
      (MachCSL.Sail.Registers.write rs .nextPC (retPC ra)) := by
  unfold jump_to _root_.Sail.SailME.run PreSail.PreSailME.run ext_control_check_pc
  simp only [retPC_aligned]
  refine returns_bind (value := Except.ok (.Retire_Success ())) ?_ (pure_plan _ _ _)
  refine returns_bind (lift_except (pure_plan (footprint shares) rs ()) ExecutionResult) ?_
  refine returns_bind (lift_except (zca_plan shares rs config) ExecutionResult) ?_
  simp only [ExceptT.bindCont, LeanPaperStock.Functions.not, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  refine returns_bind (lift_except (value := ())
    (middle := MachCSL.Sail.Registers.write rs .nextPC (retPC ra)) ?_ ExecutionResult) ?_
  · exact .write (by simp [footprint]) (.pure ⟨rfl, rfl⟩)
  · exact pure_plan _ _ _

theorem zero_link (value : BitVec 64) : wX_bits (.Regidx 0#5) value = (pure () : SailM Unit) := rfl

theorem body_eq [Platform] : body = execute_JALR 0#12 (.Regidx 1#5) (.Regidx 0#5) := rfl

theorem body_plan [Platform] (shares : Shares) (rs : RegisterFile) (config : Config rs) :
    RegisterPlan.Returns (footprint shares) rs body (.Retire_Success ()) (after rs) := by
  rw [body_eq]
  unfold execute_JALR
  refine returns_bind (elp_plan shares rs config) ?_
  refine returns_bind (read_plan shares rs .nextPC (.own 1) (by simp [footprint])) ?_
  refine returns_bind (read_plan shares rs .x1 shares.ra (by simp [footprint])) ?_
  refine returns_bind (pure_plan _ _ (rs .x1 + sign_extend (m := 64) 0#12)) ?_
  rw [retPC_jalr]
  refine returns_bind (jump_plan shares rs config (rs .x1)) ?_
  exact pure_plan _ _ _

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

theorem pc_body_plan [Platform] (shares : Shares) (pcShare : DFrac)
    (rs : RegisterFile) (config : Config rs) :
    RegisterPlan.Returns (pcFootprint shares pcShare) rs body (.Retire_Success ()) (after rs) :=
  widen (body_plan shares rs config) (fun _ member => List.mem_cons_of_mem _ member)

theorem source_body_plan [Platform] (rs : RegisterFile) (source : SourceConfig rs) :
    RegisterPlan.Returns (footprint sourceShares) rs body (.Retire_Success ()) (after rs) :=
  body_plan sourceShares rs (source_config rs source)

end Xv6.Kernel.MycpuReturn
