import Xv6.Kernel.MycpuKptState
import Xv6.Kernel.MycpuScalarGeometry

namespace Xv6.Kernel.MycpuKpt
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem phase_config {initial original old cpu k control values words}
    (config : Config initial) (phase : Phase initial original old cpu k control values words) : Config control := by
  induction phase with
  | zero => exact config
  | next bound _ done ih =>
    exact MycpuKptCycle.completed_config _ _ _ _ _ (MycpuKptCycle.started_config _ ih) done

theorem phase_stable {initial original old cpu k control values words}
    (phase : Phase initial original old cpu k control values words) : Stable initial control := by
  have same := MycpuBare.phase_stable _ _ _ (phase_reference phase).1
  intro r member
  simp only [stableControls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact same .mstatus (by decide)
  · exact same .cur_privilege (by decide)
  · exact same .misa (by decide)
  · exact same .mie (by decide)
  · exact same .mideleg (by decide)
  · exact same .menvcfg (by decide)
  · exact same .elp (by decide)
  · exact same .pma_regions (by decide)
  · exact same .htif_tohost_base (by decide)
  · exact same .hart_state (by decide)
  · exact same .mcountinhibit (by decide)
  · exact same .minstretcfg (by decide)

theorem phase_pc {initial original old cpu k control values words}
    (pc : initial .PC = MycpuDecode.address ⟨0, by decide⟩)
    (phase : Phase initial original old cpu k control values words) (bound : k < 14) :
    control .PC = MycpuDecode.address ⟨k,bound⟩ :=
  MycpuBare.phase_address (entry := entry initial cpu original) pc (phase_reference phase).1 bound

theorem phase_ready {initial original old cpu k control values words}
    (phase : Phase initial original old cpu k control values words) (bound : k < 14) :
    MycpuKptBody.StackReady ⟨k,bound⟩ (entrySP cpu original) cpu values := by
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [MycpuKptBody.StackReady, MycpuKptBody.route]
  all_goals first | trivial | skip
  all_goals
    exact ((phase_reference phase).1.core .x2 (by decide)).trans
      (MycpuBare.reference_sp _ _ (by decide) (by decide))

theorem phase_words {initial original old cpu k control values words}
    (phase : Phase initial original old cpu k control values words) : words = wordsAt cpu original old k :=
  (phase_reference phase).2

theorem final_words {initial original old cpu control values words}
    (phase : Phase initial original old cpu 14 control values words) : words = savedWords cpu original := by
  rw [phase_words phase]
  funext slot; cases slot <;> rfl

theorem sequence_projection {initial original old cpu control values words}
    (pc : initial .PC = MycpuDecode.address ⟨0, by decide⟩)
    (phase : Phase initial original old cpu 14 control values words) (r : Register)
    (member : r ∈ HartTp.physicalKeys) :
    entry control cpu values r = MycpuRegisterSequence.returned (entry initial cpu original) r := by
  have outside : r ∉ MycpuBare.ignored := by
    have disjoint : List.Disjoint HartTp.physicalKeys MycpuBare.ignored := by
      simp [List.Disjoint, show HartTp.physicalKeys = [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] from rfl, MycpuBare.ignored]
    exact disjoint member
  exact ((phase_reference phase).1.core r outside).trans
    ((MycpuBare.reference_returned (entry initial cpu original) pc) r outside).symm

theorem body_map_other (i : Fin 14) control cpu values words key
    (h1 : key ≠ 1#5) (h2 : key ≠ 2#5) (h8 : key ≠ 8#5) (h10 : key ≠ 10#5) (h15 : key ≠ 15#5) :
    MycpuKptCycle.bodyValues i control cpu values words key = values key := by
  obtain ⟨i,bound⟩ := i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [MycpuKptCycle.bodyValues, MycpuKptBody.route, MycpuKptBody.afterValues,
    MycpuKptRegister.afterValues, MycpuKptRegister.scalarIndex, MycpuKptMemory.afterMap,
    MycpuKptMemory.index, HartTp.set, h1, h2, h8, h10, h15, ite_false]

theorem phase_map_other {initial original old cpu k control values words}
    (phase : Phase initial original old cpu k control values words) key
    (h1 : key ≠ 1#5) (h2 : key ≠ 2#5) (h8 : key ≠ 8#5) (h10 : key ≠ 10#5) (h15 : key ≠ 15#5) :
    values key = original key := by
  induction phase with
  | zero => rfl
  | next bound _ _ ih => rw [body_map_other _ _ _ _ _ _ h1 h2 h8 h10 h15]; exact ih

theorem final_map_other {initial original old cpu control values words}
    (phase : Phase initial original old cpu 14 control values words) key
    (h10 : key ≠ 10#5) (h15 : key ≠ 15#5) : values key = original key := by
  have p := (phase_reference phase).1
  by_cases h1 : key = 1#5
  · subst key; exact (p.core .x1 (by decide)).trans (MycpuBare.reference_ra _ _)
  by_cases h2 : key = 2#5
  · subst key; exact (p.core .x2 (by decide)).trans (MycpuBare.reference_final_sp _)
  by_cases h8 : key = 8#5
  · subst key; exact (p.core .x8 (by decide)).trans (MycpuBare.reference_final_s0 _)
  exact phase_map_other phase key h1 h2 h8 h10 h15

theorem phase_result {initial original old cpu control values words}
    (config : Config initial) (pc : initial .PC = MycpuDecode.address ⟨0, by decide⟩)
    (phase : Phase initial original old cpu 14 control values words) : Result initial original cpu control values := by
  have p := (phase_reference phase).1
  have returnedPC : control .PC = MycpuReturn.retPC (HartTp.rget cpu original 1#5) := by
    exact p.pc.trans (MycpuBare.reference_pc (entry initial cpu original) pc 14 (by decide))
  have value : HartTp.rget cpu values 10#5 = MycpuScalar.mycpuRet (HartTp.hartWord cpu) :=
    (p.core .x10 (by decide)).trans (MycpuBare.reference_final_result (entry initial cpu original) pc)
  refine ⟨phase_config config phase, phase_stable phase, returnedPC, ?_, final_map_other phase,
    ?_, ?_, ?_, MycpuBare.phase_final_saved p, value, ?_⟩
  · exact (p.nextPC (by decide)).trans
      ((MycpuBare.reference_next_pc _ 14 (by decide)).trans p.pc.symm) |>.trans returnedPC
  · exact final_map_other phase 2#5 (by decide) (by decide)
  · exact final_map_other phase 1#5 (by decide) (by decide)
  · exact final_map_other phase 8#5 (by decide) (by decide)
  · rw [value]
    exact MycpuScalar.valid_hart cpu

theorem result_boundary initial original cpu after values (result : Result initial original cpu after values)
    (boundary : SieOffPacket.Boundary (MycpuDecode.address ⟨0, by decide⟩) initial) :
    SieOffPacket.Boundary (MycpuReturn.retPC (HartTp.rget cpu original 1#5)) after := by
  refine ⟨result.pc,result.nextPC,result.config.active,result.config.privilege,?_,?_,?_⟩
  · rw [result.stable .mie (by decide)]; exact boundary.enable
  · rw [result.stable .mideleg (by decide)]; exact boundary.delegated
  · rw [result.stable .menvcfg (by decide)]; exact boundary.environment

theorem ordered_length trace (ordered : Ordered trace) : trace.length = 14 := by
  have same := congrArg List.length ordered
  simpa using same

theorem pureSpec : PureSpec :=
  ⟨fun _ _ _ _ => .zero,
    fun _ _ _ _ _ _ _ _ => phase_bound,
    fun _ _ _ _ _ _ _ _ => phase_config,
    fun _ _ _ _ _ _ _ _ => phase_stable,
    fun _ _ _ _ _ _ _ _ => phase_pc,
    fun _ _ _ _ _ _ _ _ => phase_ready,
    fun _ _ _ _ _ _ _ _ => phase_words,
    fun _ _ _ _ _ _ _ => final_words,
    fun _ _ _ _ _ _ _ => sequence_projection,
    fun _ _ _ _ _ _ _ => phase_result,
    result_boundary, ordered_length⟩

end Xv6.Kernel.MycpuKpt
