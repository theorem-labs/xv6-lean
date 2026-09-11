import Xv6.Kernel.MycpuKptRegisterSpec
import Xv6.Kernel.MycpuScalarProofs
import Xv6.Kernel.MycpuReturnProofs
import Xv6.Kernel.MycpuRegimeShellPlan

namespace Xv6.Kernel.MycpuKptRegister
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem scalar_body [Platform] (i : Fin 9) : body (.scalar i) = MycpuScalar.body i := rfl
theorem return_body [Platform] : body .returns = MycpuReturn.body := rfl

theorem scalar_physical (i : Fin 9) : HartTp.physical (scalarIndex i) = some (scalarRegister i) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem scalar_nonzero (i : Fin 9) : scalarIndex i ≠ 0#5 ∧ scalarIndex i ≠ HartTp.tp := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [scalarIndex, HartTp.tp]

theorem scalar_entry (i : Fin 9) (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile) :
    entry (afterControl (.scalar i) control cpu values) cpu (afterValues (.scalar i) control cpu values) =
      MycpuScalar.after i (entry control cpu values) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals funext r; cases r <;> rfl

theorem return_entry (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile) :
    entry (afterControl .returns control cpu values) cpu (afterValues .returns control cpu values) =
      MycpuReturn.after (entry control cpu values) := by
  funext r
  cases r <;> rfl

theorem scalar_other i control cpu values key (different : key ≠ scalarIndex i) :
    afterValues (.scalar i) control cpu values key = values key :=
  HartTp.set_other values (scalarIndex i) key _ different

theorem zero (instruction : Instruction) control cpu values :
    afterValues instruction control cpu values 0#5 = values 0#5 := by
  cases instruction with
  | returns => rfl
  | scalar i => exact scalar_other i control cpu values _ (Ne.symm (scalar_nonzero i).1)

theorem pinned_tp (instruction : Instruction) control cpu values :
    HartTp.rget cpu (afterValues instruction control cpu values) HartTp.tp = HartTp.hartWord cpu := by
  simp [HartTp.rget, HartTp.pin, HartTp.set]

theorem status (instruction : Instruction) control cpu values :
    afterControl instruction control cpu values .mstatus = control .mstatus := by
  cases instruction <;> rfl

theorem physical_pc (instruction : Instruction) control cpu values :
    afterControl instruction control cpu values .PC = control .PC := by
  cases instruction <;> rfl

theorem return_target control cpu values :
    afterControl .returns control cpu values .nextPC = MycpuReturn.retPC (HartTp.rget cpu values 1#5) := by
  simp [afterControl]

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

theorem scalar_members (shares : Shares) cell (member : cell ∈ MycpuScalar.footprint (.own 1) (.own 1)) :
    cell ∈ MycpuRegimeShell.footprint shares := by
  simp only [MycpuScalar.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint, show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl, MycpuOff.gpr_list]

theorem return_members (shares : Shares) cell
    (member : cell ∈ MycpuReturn.footprint ⟨.own 1,shares.privilege,shares.environment,shares.misa⟩) :
    cell ∈ MycpuRegimeShell.footprint shares := by
  simp only [MycpuReturn.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals simp [MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint, show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl, MycpuOff.gpr_list]

theorem body_plan [Platform] instruction shares control cpu values (config : Config instruction control) :
    RegisterPlan.Returns (MycpuRegimeShell.footprint shares) (entry control cpu values)
      (body instruction) (.Retire_Success ())
      (entry (afterControl instruction control cpu values) cpu (afterValues instruction control cpu values)) := by
  cases instruction with
  | scalar i =>
    rw [scalar_body, scalar_entry]
    exact widen (MycpuScalar.body_plan (.own 1) (.own 1) i (entry control cpu values)) (scalar_members shares)
  | returns =>
    rw [return_body, return_entry]
    have actual : MycpuReturn.Config (entry control cpu values) :=
      ⟨config.privilege, config.lpe, config.compressed⟩
    exact widen (MycpuReturn.body_plan ⟨.own 1,shares.privilege,shares.environment,shares.misa⟩
      (entry control cpu values) actual) (return_members shares)

theorem pureSpec [Platform] : PureSpec :=
  ⟨scalar_body, return_body, scalar_physical, scalar_nonzero, scalar_entry, return_entry,
    scalar_other, zero, pinned_tp, status, physical_pc, return_target, body_plan⟩

end Xv6.Kernel.MycpuKptRegister
