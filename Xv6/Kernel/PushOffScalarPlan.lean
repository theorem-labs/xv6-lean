import Xv6.Kernel.PushOffScalarPure
import Xv6.Kernel.MycpuKptRegisterPure

namespace Xv6.Kernel.PushOffScalar
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem returns_bind {fp rs middle after} {program : SailM α} {next : α → SailM β} {value final}
    (first : RegisterPlan.Returns fp rs program value middle)
    (rest : RegisterPlan.Returns fp middle (next value) final after) :
    RegisterPlan.Returns fp rs (program >>= next) final after :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl,rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl,rfl⟩

private theorem read_plan shares rs r dq (member : (r,dq) ∈ MycpuRegimeShell.footprint shares) :
    RegisterPlan.Returns (MycpuRegimeShell.footprint shares) rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl,rfl⟩)

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs middle : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value middle) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) middle := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) middle
  exact returns_bind plan (pure_plan fp middle _)

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

/-- Only MISA is physically read by this eager compressed-alignment check. -/
theorem zca_plan shares rs (compressed : _get_Misa_C (rs .misa) = 1#1) :
    RegisterPlan.Returns (MycpuRegimeShell.footprint shares) rs (currentlyEnabled .Ext_Zca) true rs := by
  have inner : RegisterPlan.Returns (MycpuRegimeShell.footprint shares) rs
      (currentlyEnabled .Ext_C) true rs := by
    unfold currentlyEnabled
    refine returns_bind (read_plan shares rs .misa shares.misa (by
      simp [MycpuRegimeShell.footprint,MycpuRegimeShell.controlFootprint])) ?_
    rw [compressed,show hartSupports .Ext_C = true by simp [hartSupports,LeanPaperStock.Functions.not,LeanPaperStock.Functions.xlen]]
    exact pure_plan _ _ _
  unfold currentlyEnabled
  refine returns_bind inner ?_
  rw [show hartSupports .Ext_Zca = true by unfold hartSupports; rfl,
    show hartSupports .Ext_C = true by simp [hartSupports,LeanPaperStock.Functions.not,LeanPaperStock.Functions.xlen]]
  exact pure_plan _ _ _

/-- Real assertion and eager MISA read are retained before the nextPC write. -/
theorem jump_plan shares rs target (compressed : _get_Misa_C (rs .misa) = 1#1)
    (even : Sail.BitVec.access target 0 = 0#1) :
    RegisterPlan.Returns (MycpuRegimeShell.footprint shares) rs (jump_to target) (.Retire_Success ())
      (MachCSL.Sail.Registers.write rs .nextPC target) := by
  unfold jump_to _root_.Sail.SailME.run PreSail.PreSailME.run ext_control_check_pc
  simp only [even]
  refine returns_bind (value := Except.ok (.Retire_Success ())) ?_ (pure_plan _ _ _)
  refine returns_bind (lift_except (pure_plan (MycpuRegimeShell.footprint shares) rs ()) ExecutionResult) ?_
  refine returns_bind (lift_except (zca_plan shares rs compressed) ExecutionResult) ?_
  simp only [ExceptT.bindCont,LeanPaperStock.Functions.not,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte]
  refine returns_bind (lift_except (value := ())
    (middle := MachCSL.Sail.Registers.write rs .nextPC target) ?_ ExecutionResult) ?_
  · exact .write (by simp [MycpuRegimeShell.footprint,MycpuRegimeShell.controlFootprint,
      SupervisorRetirement.pcFootprint]) (.pure ⟨rfl,rfl⟩)
  · exact pure_plan _ _ _

/-- Kernel-checked selection of the actual generated instruction body. -/
theorem body_eq [Platform] (i : Instruction) : body i =
    (match i with
    | .subSP => do
      _root_.Sail.writeReg .x2 ((← _root_.Sail.readReg .x2) + sign_extend (m := 64) 0xfe0#12)
      pure (.Retire_Success ())
    | .framePointer => do
      _root_.Sail.writeReg .x8 ((← _root_.Sail.readReg .x2) + 32#64)
      pure (.Retire_Success ())
    | .saveStatus => do
      _root_.Sail.writeReg .x9 (0#64 + (← _root_.Sail.readReg .x15))
      pure (.Retire_Success ())
    | .branchZero => do
      let value ← _root_.Sail.readReg .x15
      if value == 0#64 then jump_to ((← _root_.Sail.readReg .PC) + sign_extend (m := 64) 22#13)
      else pure (.Retire_Success ())
    | .increment => do
      _root_.Sail.writeReg .x15 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((← _root_.Sail.readReg .x15) + 1#64) 31 0))
      pure (.Retire_Success ())
    | .restoreSP => do
      _root_.Sail.writeReg .x2 ((← _root_.Sail.readReg .x2) + 32#64)
      pure (.Retire_Success ())
    | .returns => MycpuReturn.body
    | .shift => do
      _root_.Sail.writeReg .x15 (_root_.Sail.shift_bits_right (← _root_.Sail.readReg .x9) 1#6)
      pure (.Retire_Success ())
    | .mask => do
      _root_.Sail.writeReg .x15 ((← _root_.Sail.readReg .x15) &&& 1#64)
      pure (.Retire_Success ())
    | .jumpBack => do
      let link ← get_next_pc ()
      let pc ← _root_.Sail.readReg .PC
      match ← jump_to (pc + sign_extend (m := 64) 0x1fffe0#21) with
      | .Retire_Success () => wX_bits (.Regidx 0#5) link >>= fun _ => pure (.Retire_Success ())
      | failure => pure failure) := by
  cases i
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

/-- Every branch decision is obtained from its actual register read. -/
theorem register_plan [Platform] (i : Instruction) shares rs (config : Config i rs) :
    RegisterPlan.Returns (MycpuRegimeShell.footprint shares) rs (body i) (.Retire_Success ()) (after i rs) := by
  rw [body_eq]
  cases i with
  | subSP | framePointer | saveStatus | increment | restoreSP | shift | mask =>
    all_goals
      exact .read (dq := .own 1) (by simp [MycpuRegimeShell.footprint,
        show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl,MycpuOff.gpr_list])
        (.write (by simp [MycpuRegimeShell.footprint,
          show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl,MycpuOff.gpr_list]) (.pure ⟨rfl,rfl⟩))
  | returns =>
    exact widen (MycpuReturn.body_plan ⟨.own 1,shares.privilege,shares.environment,shares.misa⟩ rs config)
      (MycpuKptRegister.return_members shares)
  | branchZero =>
    change RegisterPlan.Returns _ rs
      (PreSail.readReg .x15 >>= fun value => if value == 0#64 then
        (PreSail.readReg .PC >>= fun pc => jump_to (pc + sign_extend (m := 64) 22#13))
        else pure (.Retire_Success ())) _ _
    refine returns_bind (read_plan shares rs .x15 (.own 1) (by simp [MycpuRegimeShell.footprint,
      show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl,MycpuOff.gpr_list])) ?_
    change RegisterPlan.Returns _ rs
      (if rs .x15 == 0#64 then (PreSail.readReg .PC >>= fun pc => jump_to (pc + sign_extend (m := 64) 22#13))
        else pure (.Retire_Success ())) _
      (if rs .x15 == 0#64 then MachCSL.Sail.Registers.write rs .nextPC (rs .PC + 22#64) else rs)
    by_cases taken : rs .x15 == 0#64
    · rw [if_pos taken, if_pos taken]
      refine returns_bind (read_plan shares rs .PC (.own 1) (by simp [MycpuRegimeShell.footprint,
        MycpuRegimeShell.controlFootprint,SupervisorRetirement.pcFootprint])) ?_
      exact jump_plan shares rs _ config.1 (add_even _ 22#64 config.2 (by decide))
    · rw [if_neg taken, if_neg taken]
      exact pure_plan _ _ _
  | jumpBack =>
    change RegisterPlan.Returns _ rs
      (get_next_pc () >>= fun link => PreSail.readReg .PC >>= fun pc =>
        jump_to (pc + sign_extend (m := 64) 0x1fffe0#21) >>= fun result => match result with
        | .Retire_Success () => wX_bits (.Regidx 0#5) link >>= fun _ => pure (.Retire_Success ())
        | failure => pure failure) _ _
    refine returns_bind (read_plan shares rs .nextPC (.own 1) (by simp [MycpuRegimeShell.footprint,
      MycpuRegimeShell.controlFootprint,SupervisorRetirement.pcFootprint])) ?_
    refine returns_bind (read_plan shares rs .PC (.own 1) (by simp [MycpuRegimeShell.footprint,
      MycpuRegimeShell.controlFootprint,SupervisorRetirement.pcFootprint])) ?_
    refine returns_bind (jump_plan shares rs _ config.1 (add_even _ _ config.2 (by decide))) ?_
    exact pure_plan _ _ _

theorem body_plan [Platform] i shares control cpu values (config : Config i control) :
    RegisterPlan.Returns (MycpuRegimeShell.footprint shares) (entry control cpu values)
      (body i) (.Retire_Success ())
      (entry (afterControl i control cpu values) cpu (afterValues i cpu values)) := by
  rw [after_entry]
  apply register_plan
  cases i <;> try exact config
  exact ⟨config.privilege, config.lpe, config.compressed⟩

theorem pureSpec [Platform] : PureSpec :=
  ⟨inventory,after_entry,other,zero,pinned_tp,control_other,source_config,
    branch_taken,branch_not_taken,jump_target,return_target,body_plan⟩

end Xv6.Kernel.PushOffScalar
