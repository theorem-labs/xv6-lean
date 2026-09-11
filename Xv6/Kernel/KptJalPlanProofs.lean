import Xv6.Kernel.KptJalSpec
import Xv6.Kernel.MycpuKptCycleLink
import Xv6.Kernel.MycpuReturnProofs

namespace Xv6.Kernel.KptJal
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

private theorem read_plan shares rs r dq (member : (r,dq) ∈ footprint shares) :
    RegisterPlan.Returns (footprint shares) rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl,rfl⟩)

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs middle : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value middle) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) middle := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) middle
  exact returns_bind plan (pure_plan fp middle _)

theorem jump_plan shares rs (config : Config rs) (jumpTarget : BitVec 64)
    (even : Sail.BitVec.access jumpTarget 0 = 0#1) :
    RegisterPlan.Returns (footprint shares) rs (jump_to jumpTarget) (.Retire_Success ())
      (MachCSL.Sail.Registers.write rs .nextPC jumpTarget) := by
  unfold jump_to _root_.Sail.SailME.run PreSail.PreSailME.run ext_control_check_pc
  simp only [even]
  refine returns_bind (value := Except.ok (.Retire_Success ())) ?_ (pure_plan _ _ _)
  refine returns_bind (lift_except (pure_plan (footprint shares) rs ()) ExecutionResult) ?_
  refine returns_bind (lift_except (MycpuKptCycle.zca_plan shares rs (MycpuKptCycle.compressed_config rs config)) ExecutionResult) ?_
  simp only [ExceptT.bindCont,LeanPaperStock.Functions.not,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte]
  refine returns_bind (lift_except (value := ())
    (middle := MachCSL.Sail.Registers.write rs .nextPC jumpTarget) ?_ ExecutionResult) ?_
  · exact .write (by simp [footprint,MycpuRegimeShell.footprint,MycpuRegimeShell.controlFootprint,
      SupervisorRetirement.pcFootprint]) (.pure ⟨rfl,rfl⟩)
  · exact pure_plan _ _ _

theorem execute_factor [Platform] imm : execute (instruction imm) =
    (get_next_pc () >>= fun returnAddress => PreSail.readReg .PC >>= fun pc =>
      jump_to (target pc imm) >>= fun execution => match execution with
      | .Retire_Success () => wX_bits (.Regidx 1#5) returnAddress >>= fun _ => pure (.Retire_Success ())
      | failure => pure failure) := rfl

theorem prepared_entry pc control cpu values :
    prepared pc (entry control cpu values) = entry (prepared pc control) cpu values := by
  funext r; cases r <;> rfl

theorem after_prepared pc imm control : afterControl pc imm (prepared pc control) = afterControl pc imm control := by
  funext r; cases r <;> rfl

theorem after_entry pc imm control cpu values :
    entry (afterControl pc imm control) cpu (afterValues pc values) =
      MachCSL.Sail.Registers.write (MachCSL.Sail.Registers.write (entry control cpu values) .nextPC (target pc imm)) .x1 (link pc) := by
  funext r; cases r <;> rfl

theorem ra pc cpu values : HartTp.rget cpu (afterValues pc values) 1#5 = link pc := by rfl

theorem other pc cpu values index (different : index ≠ 1#5) :
    HartTp.rget cpu (afterValues pc values) index = HartTp.rget cpu values index := by
  simp [HartTp.rget,HartTp.pin,afterValues,HartTp.set,different]

theorem zero pc values : afterValues pc values 0#5 = values 0#5 := rfl

theorem prepared_config pc control (h : Config control) : Config (prepared pc control) :=
  ⟨h.privilege,h.active,h.landing,h.misa,h.environment,h.delegated,h.pma,h.htif⟩

theorem after_config pc imm control (h : Config control) : Config (afterControl pc imm control) :=
  ⟨h.privilege,h.active,h.landing,h.misa,h.environment,h.delegated,h.pma,h.htif⟩

theorem completed_config pc imm control after (h : Config control)
    (done : MycpuRegimeShell.Completed (afterControl pc imm control) after) : Config after := by
  have p := after_config pc imm control h
  have unchanged := MycpuCycleShell.completed_other _ _ done
  constructor
  · rw [unchanged .cur_privilege (by decide) (by decide) (by decide)]; exact p.privilege
  · rw [unchanged .hart_state (by decide) (by decide) (by decide)]; exact p.active
  · rw [unchanged .elp (by decide) (by decide) (by decide)]; exact p.landing
  · rw [unchanged .misa (by decide) (by decide) (by decide)]; exact p.misa
  · rw [unchanged .menvcfg (by decide) (by decide) (by decide)]; exact p.environment
  · rw [unchanged .mie (by decide) (by decide) (by decide),unchanged .mideleg (by decide) (by decide) (by decide)]
    exact p.delegated
  · rw [unchanged .pma_regions (by decide) (by decide) (by decide)]; exact p.pma
  · rw [unchanged .htif_tohost_base (by decide) (by decide) (by decide)]; exact p.htif

theorem completed_pc pc imm control after (done : MycpuRegimeShell.Completed (afterControl pc imm control) after) :
    after .PC = target pc imm ∧ after .nextPC = target pc imm :=
  MycpuCycleShell.completed_pc _ _ done

theorem body_plan [Platform] shares control cpu values pc imm (config : Config control)
    (atPC : control .PC = pc) (atNext : control .nextPC = link pc) (even : TargetEven pc imm) :
    RegisterPlan.Returns (footprint shares) (entry control cpu values) (body imm) (.Retire_Success ())
      (entry (afterControl pc imm control) cpu (afterValues pc values)) := by
  rw [after_entry]
  unfold body
  rw [execute_factor]
  simp only [BootPmp.sail_bind_assoc]
  refine returns_bind (read_plan shares (entry control cpu values) .nextPC (.own 1) (by
    simp [footprint,MycpuRegimeShell.footprint,MycpuRegimeShell.controlFootprint,SupervisorRetirement.pcFootprint])) ?_
  refine returns_bind (read_plan shares (entry control cpu values) .PC (.own 1) (by
    simp [footprint,MycpuRegimeShell.footprint,MycpuRegimeShell.controlFootprint,SupervisorRetirement.pcFootprint])) ?_
  change RegisterPlan.Returns _ _ (jump_to (target (control .PC) imm) >>= _) _ _
  rw [atPC]
  refine returns_bind (jump_plan shares _ (MycpuKptCycle.entry_config control cpu values config) _ even) ?_
  change RegisterPlan.Returns _ _ (PreSail.writeReg .x1 (control .nextPC) >>= _) _ _
  rw [atNext]
  exact .write (by simp [footprint,MycpuRegimeShell.footprint,show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl,MycpuOff.gpr_list])
    (.pure ⟨rfl,rfl⟩)

end Xv6.Kernel.KptJal
