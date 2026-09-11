import Xv6.Kernel.KptJalDecodeProofs

namespace Xv6.Kernel.KptJal
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000


private theorem returns_bind {fp : RegisterFootprint.Footprint} {rs middle after : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value middle)
    (rest : RegisterPlan.Returns fp middle (next value) result after) :
    RegisterPlan.Returns fp rs (program >>= next) result after :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl,rfl⟩ => rest

/-- Actual two-register decoder plan, with both preceding extension checks. -/
theorem decoder shares control imm (config : Config control) (even : Encodable imm) :
    RegisterPlan.Returns (footprint shares) control (ext_decode (encoding imm)) (instruction imm) control := by
  rw [decode_factor imm even]
  rw [show currentlyEnabled .Ext_Zihintpause = (pure true : SailM Bool) by
    unfold currentlyEnabled hartSupports; rfl]
  simp only [BootPmp.sail_pure_bind]
  have enabled : RegisterPlan.Returns (footprint shares) control (currentlyEnabled .Ext_Zicfilp) false control := by
    unfold currentlyEnabled
    rw [show currentlyEnabled .Ext_Zicsr = (pure true : SailM Bool) by
      unfold currentlyEnabled
      rw [show hartSupports .Ext_Zicsr = true by unfold hartSupports; rfl]]
    simp only [BootPmp.sail_pure_bind]
    refine returns_bind (value := control .cur_privilege) (middle := control)
      (.read (dq := shares.privilege) (by simp [footprint,MycpuRegimeShell.footprint,
        MycpuRegimeShell.controlFootprint]) (.pure ⟨rfl,rfl⟩)) ?_
    rw [config.privilege]
    have inner : RegisterPlan.Returns (footprint shares) control (get_xLPE .Supervisor) false control := by
      unfold get_xLPE
      refine returns_bind (value := control .menvcfg) (middle := control)
        (.read (dq := shares.environment) (by simp [footprint,MycpuRegimeShell.footprint,
          MycpuRegimeShell.controlFootprint]) (.pure ⟨rfl,rfl⟩)) ?_
      rw [config.environment]
      exact .pure ⟨rfl,rfl⟩
    refine returns_bind inner ?_
    rw [show hartSupports .Ext_Zicfilp = true by unfold hartSupports; rfl]
    exact .pure ⟨rfl,rfl⟩
  exact returns_bind enabled (.pure ⟨rfl,rfl⟩)

private theorem run_tail [Platform] imm :
    _root_.Sail.SailME.run (do
      let result ← ((do
        match (← execute (instruction imm)) with
        | .ExecuteAs other => execute other
        | result => pure result) : SailME Step ExecutionResult)
      pure (Step.Step_Execute (result,encoding imm))) = executeTail imm := by
  apply (MycpuActive.execute_run (instruction imm) (encoding imm)).trans
  unfold executeTail body
  rw [BootPmp.sail_bind_assoc]
  congr 1
  funext result
  cases result <;> rfl

theorem prepare_plan [Platform] shares control cpu values pc imm (config : Config control)
    (atPC : control .PC = pc) (even : Encodable imm) :
    MycpuActive.Prefix (footprint shares) (entry control cpu values)
      (MycpuActive.afterFetch 0 (result imm)) (executeTail imm) (entry (prepared pc control) cpu values) := by
  have rsConfig := MycpuKptCycle.entry_config control cpu values config
  have decode := decoder shares (entry control cpu values) imm rsConfig even
  have land := MycpuKptCycle.landing_plan shares (entry control cpu values) config.landing
  have readPC : RegisterPlan.Returns (footprint shares) (entry control cpu values)
      (PreSail.readReg .PC) pc (entry control cpu values) := by
    rw [← atPC]
    exact .read (dq := .own 1) (by simp [footprint,MycpuRegimeShell.footprint,
      MycpuRegimeShell.controlFootprint,SupervisorRetirement.pcFootprint]) (.pure ⟨rfl,rfl⟩)
  have writePC : RegisterPlan.Returns (footprint shares) (entry control cpu values)
      (PreSail.writeReg .nextPC (link pc)) () (entry (prepared pc control) cpu values) := by
    rw [← prepared_entry]
    exact .write (by simp [footprint,MycpuRegimeShell.footprint,
      MycpuRegimeShell.controlFootprint,SupervisorRetirement.pcFootprint]) (.pure ⟨rfl,rfl⟩)
  simp only [MycpuActive.afterFetch,result,ext_fetch_hook]
  rw [MycpuActive.run_lift_bind]
  refine .prefix decode ?_
  simp only [get_config_print_instr,Bool.false_eq_true,↓reduceIte]
  rw [MycpuActive.run_lift_bind]
  refine .prefix land ?_
  simp only [Bool.false_and,Bool.false_eq_true,↓reduceIte]
  rw [MycpuActive.run_lift_bind]
  refine .prefix readPC ?_
  rw [MycpuActive.run_lift_bind]
  refine .prefix writePC ?_
  have bits : zero_extend (m := 32) (encoding imm) = encoding imm := by
    simp [zero_extend,Sail.BitVec.zeroExtend]
  rw [bits]
  exact Eq.mp (congrArg (fun program => MycpuActive.Prefix (footprint shares)
    (entry (prepared pc control) cpu values) program (executeTail imm)
    (entry (prepared pc control) cpu values)) (run_tail imm).symm) .done

theorem pureSpec [Platform] : PureSpec :=
  ⟨encoder,base,immediate_even,decoder,execute_factor,prepare_plan,body_plan,prepared_entry,
    after_prepared,ra,other,zero,MycpuKptCycle.started_config,prepared_config,after_config,
    completed_config,completed_pc⟩

end Xv6.Kernel.KptJal
