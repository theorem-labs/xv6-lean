import Xv6.Kernel.MycpuKptBodySpec
import Xv6.Kernel.MycpuKptRegisterPure
import Xv6.Kernel.MycpuKptMemoryPure

namespace Xv6.Kernel.MycpuKptBody
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 10000
set_option maxHeartbeats 20000

theorem route_index (i : Fin 14) : routeIndex (route i) = i := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem body_route [Platform] (i : Fin 14) : body i = routedBody (route i) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem ra_address (entrySP : BitVec 64) : slotAddress entrySP .ra = entrySP - 8#64 := by
  change (entrySP - 16#64) + 8#64 = entrySP - 8#64
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem s0_address (entrySP : BitVec 64) : slotAddress entrySP .s0 = entrySP - 16#64 := by
  change (entrySP - 16#64) + 0#64 = _
  exact BitVec.add_zero _

theorem memory_address i entrySP cpu values kind slot
    (h : route i = .memory kind slot) (ready : StackReady i entrySP cpu values) :
    MycpuKptMemory.address cpu values slot = slotAddress entrySP slot := by
  simp only [StackReady, h] at ready
  unfold MycpuKptMemory.address slotAddress
  rw [ready]

theorem phase_ready (i : Fin 14) entrySP cpu values
    (sp : HartTp.rget cpu values 2#5 = phaseSP i entrySP) : StackReady i entrySP cpu values := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [StackReady, route, phaseSP]

theorem scalar_sp_projection (i : Fin 9) control cpu values :
    HartTp.rget cpu (MycpuKptRegister.afterValues (.scalar i) control cpu values) 2#5 =
      MycpuScalar.after i (entry control cpu values) .x2 :=
  congrFun (MycpuKptRegister.scalar_entry i control cpu values) .x2

theorem scalar_sp_other (i : Fin 9) control cpu values (h : 2#5 ≠ MycpuKptRegister.scalarIndex i) :
    HartTp.rget cpu (MycpuKptRegister.afterValues (.scalar i) control cpu values) 2#5 =
      HartTp.rget cpu values 2#5 :=
  MycpuKptRegister.scalar_other i control cpu values 2#5 h

theorem phase_step (i : Fin 14) entrySP control cpu values words
    (sp : HartTp.rget cpu values 2#5 = phaseSP i entrySP) :
    HartTp.rget cpu (afterValues (route i) control cpu values words) 2#5 = nextSP i entrySP := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [route, afterValues]
    rw [scalar_sp_projection]
    change HartTp.rget cpu values 2#5 + (-16#64) = entrySP - 16#64
    change HartTp.rget cpu values 2#5 = entrySP at sp
    rw [sp, BitVec.sub_eq_add_neg]
  · simp only [route, afterValues]
    rw [MycpuKptMemory.after_sp]
    exact sp
  · simp only [route, afterValues]
    rw [MycpuKptMemory.after_sp]
    exact sp
  · simp only [route, afterValues]
    rw [scalar_sp_other _ _ _ _ (by decide)]
    exact sp
  · simp only [route, afterValues]
    rw [scalar_sp_other _ _ _ _ (by decide)]
    exact sp
  · simp only [route, afterValues]
    rw [scalar_sp_other _ _ _ _ (by decide)]
    exact sp
  · simp only [route, afterValues]
    rw [scalar_sp_other _ _ _ _ (by decide)]
    exact sp
  · simp only [route, afterValues]
    rw [scalar_sp_other _ _ _ _ (by decide)]
    exact sp
  · simp only [route, afterValues]
    rw [scalar_sp_other _ _ _ _ (by decide)]
    exact sp
  · simp only [route, afterValues]
    rw [scalar_sp_other _ _ _ _ (by decide)]
    exact sp
  · simp only [route, afterValues]
    rw [MycpuKptMemory.after_sp]
    exact sp
  · simp only [route, afterValues]
    rw [MycpuKptMemory.after_sp]
    exact sp
  · simp only [route, afterValues]
    rw [scalar_sp_projection]
    change HartTp.rget cpu values 2#5 + 16#64 = entrySP
    change HartTp.rget cpu values 2#5 = entrySP - 16#64 at sp
    rw [sp, BitVec.sub_add_cancel]
  · exact sp

theorem physical_pc i control cpu values : afterControl (route i) control cpu values .PC = control .PC := by
  cases route i with
  | registers instruction => exact MycpuKptRegister.physical_pc instruction control cpu values
  | memory kind slot => rfl

theorem next_pc (i : Fin 14) control cpu values (h : i.val ≠ 13) :
    afterControl (route i) control cpu values .nextPC = control .nextPC := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | contradiction

theorem return_pc control cpu values :
    afterControl (route ⟨13, by decide⟩) control cpu values .nextPC =
      MycpuReturn.retPC (HartTp.rget cpu values 1#5) :=
  MycpuKptRegister.return_target control cpu values

theorem pureSpec [Platform] : PureSpec :=
  ⟨route_index, body_route, ra_address, s0_address, memory_address, phase_ready,
    phase_step, physical_pc, next_pc, return_pc, rfl, fun _ => rfl, fun _ _ => rfl⟩

end Xv6.Kernel.MycpuKptBody
