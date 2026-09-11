import Xv6.Kernel.MycpuKptWitnessImageProofs
namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem initial_eq : stateAt 0 = initial := by
  change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

theorem checkpoint_other (k : Nat) (r : Register) (htlb : r ≠ .tlb) (hret : r ≠ .minstret) :
    checkpoint k r = MycpuBare.reference entry k r := by
  simp only [checkpoint, Sail.Registers.write_other _ _ _ _ (Ne.symm htlb),
    Sail.Registers.write_other _ _ _ _ (Ne.symm hret)]

theorem checkpoint_stable (k : Nat) : MycpuBare.Stable entry (checkpoint k) := by
  have phase : MycpuBare.Phase entry k (MycpuBare.reference entry k) := ⟨.refl _, rfl, fun _ => rfl⟩
  have stable := MycpuBare.phase_stable entry k _ phase
  intro r member
  have different : r ≠ .tlb ∧ r ≠ .minstret := by
    simp only [MycpuBare.stableRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  rw [checkpoint_other k r different.1 different.2]
  exact stable r member

theorem checkpoint_saved : CalleeSaved.Preserved entry (checkpoint 14) := by
  have phase : MycpuBare.Phase entry 14 (MycpuBare.reference entry 14) := ⟨.refl _, rfl, fun _ => rfl⟩
  have saved := MycpuBare.phase_final_saved phase
  intro r member
  have different : r ≠ .tlb ∧ r ≠ .minstret := by
    simp only [CalleeSaved.registers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  rw [checkpoint_other 14 r different.1 different.2]
  exact saved r member

theorem result : Result (stateAt 14).registers where
  exact_file := rfl
  stable := checkpoint_stable 14
  saved := checkpoint_saved
  ra := by
    change checkpoint 14 .x1 = _
    rw [checkpoint_other _ _ (by decide) (by decide)]
    exact MycpuBare.reference_ra entry 14
  pc := by
    change checkpoint 14 .PC = _
    rw [checkpoint_other _ _ (by decide) (by decide)]
    exact MycpuBare.reference_pc entry rfl 14 (by decide)
  nextPC := by
    change checkpoint 14 .nextPC = _
    rw [checkpoint_other _ _ (by decide) (by decide), MycpuBare.reference_next_pc entry 14 (by decide)]
    exact MycpuBare.reference_pc entry rfl 14 (by decide)
  value := by
    change checkpoint 14 .x10 = _
    rw [checkpoint_other _ _ (by decide) (by decide)]
    exact MycpuBare.reference_final_result entry rfl
  cpuAddress := by rfl
  sv39 := (checkpoint_stable 14 .satp (by simp [MycpuBare.stableRegisters]))
  tlb := by rfl

theorem values : readBytes (stateAt 14).memory (MycpuBare.raSlot entry) 8 = some (entry .x1) ∧
    readBytes (stateAt 14).memory (MycpuBare.s0Slot entry) 8 = some (entry .x8) ∧
    (stateAt 14).log.length = 2 ∧ (stateAt 14).registers .minstret = 14#64 ∧
    (stateAt 14).registers .mcycle = 0#64 ∧ (stateAt 14).registers .mtime = 0#64 := by
  repeat constructor
  all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem configured_focus : focus configured cpu = initial := by
  simp only [focus, configured, updateHart_same]
  rfl

theorem configured_others : othersReserved configured.reservations cpu = fun _ => False := by
  funext address
  apply propext
  simp [othersReserved, reservationDomain, configured, MycpuBareWitness.configured]

theorem global_frame : (∀ other, other ≠ cpu → finalState.registers other = configured.registers other) ∧
    finalState.devices = configured.devices ∧ finalState.image = image ∧
    finalState.reservations = configured.reservations ∧ finalState.views = configured.views ∧
    finalState.power = true ∧ finalState.generation = 0 := by
  refine ⟨?_, rfl, rfl, ?_, ?_, rfl, rfl⟩
  · intro other different
    exact updateHart_other _ _ _ _ different
  · change updateHart (fun _ : CPU => none) cpu none = _
    exact updateHart_self _ _
  · change updateHart (fun _ : CPU => 0) cpu 0 = _
    exact updateHart_self _ _

end Xv6.Kernel.MycpuKptWitness
