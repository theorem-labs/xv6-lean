import Xv6.Kernel.MycpuBareWitnessRunProofs

namespace Xv6.Kernel.MycpuBareWitness
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

theorem result : MycpuBare.Result entry (stateAt 14).registers := by
  apply MycpuBare.phase_result entry_config
  refine ⟨MycpuBare.CoreEq.write_ignored _ .minstret _ (by decide), ?_, ?_⟩
  · exact Sail.Registers.write_other (MycpuBare.reference entry 14) Register.minstret Register.PC (BitVec.ofNat 64 14) (by decide)
  · intro _
    exact Sail.Registers.write_other (MycpuBare.reference entry 14) Register.minstret Register.nextPC (BitVec.ofNat 64 14) (by decide)

theorem values : (stateAt 14).registers .x1 = entry .x1 ∧
    (stateAt 14).registers .x8 = entry .x8 ∧
    (stateAt 14).registers .x2 = entry .x2 ∧
    (stateAt 14).registers .x10 = 0x80012568#64 ∧
    readBytes (stateAt 14).memory (MycpuBare.raSlot entry) 8 = some (entry .x1) ∧
    readBytes (stateAt 14).memory (MycpuBare.s0Slot entry) 8 = some (entry .x8) ∧
    (stateAt 14).log.length = 2 := by
  repeat constructor
  all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem code_ra_disjoint : ∀ (j : Fin 34) (k : Fin 8),
    addressAdd (MycpuBare.raSlot entry) k.val ≠
      BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int)) := by decide

private theorem code_s0_disjoint : ∀ (j : Fin 34) (k : Fin 8),
    addressAdd (MycpuBare.s0Slot entry) k.val ≠
      BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int)) := by decide

theorem code (j : Fin 34) :
    (stateAt 14).memory (BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int))) =
      image (BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int))) := by
  change writeBytes (writeBytes image (MycpuBare.raSlot entry) 8 (entry .x1))
    (MycpuBare.s0Slot entry) 8 (entry .x8) _ = _
  rw [writeBytes_outside _ _ _ _ _ (by
    rintro ⟨k, hk, eq⟩; exact code_s0_disjoint j ⟨k, hk⟩ eq)]
  exact writeBytes_outside _ _ _ _ _ (by
    rintro ⟨k, hk, eq⟩; exact code_ra_disjoint j ⟨k, hk⟩ eq)

theorem scratch_initial :
    readBytes initial.memory (MycpuBare.raSlot entry) 8 = some 0 ∧
    readBytes initial.memory (MycpuBare.s0Slot entry) 8 = some 0 := by
  change readBytes image _ _ = _ ∧ readBytes image _ _ = _
  rw [← cached_image]
  constructor <;> rfl

theorem final_counters : (stateAt 14).registers .minstret = 14#64 ∧
    (stateAt 14).registers .mcycle = 0#64 ∧
    (stateAt 14).registers .mtime = 0#64 ∧
    (stateAt 14).view = 0 ∧ (stateAt 14).reservation = none := by
  repeat constructor
  all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem configured_focus : focus configured cpu = initial := by
  simp only [focus, configured, updateHart_same]
  rfl

theorem configured_others : othersReserved configured.reservations cpu = fun _ => False := by
  funext address
  apply propext
  simp [othersReserved, reservationDomain, configured]

/-- Explicit global frame: the run's selected-hart write-back keeps every other
hart file and all device state, the image, power and generation. -/
theorem global_frame :
    (∀ other, other ≠ cpu → (writeBack configured cpu (stateAt 14)).registers other =
      configured.registers other) ∧
    (writeBack configured cpu (stateAt 14)).devices = configured.devices ∧
    (writeBack configured cpu (stateAt 14)).image = image ∧
    (writeBack configured cpu (stateAt 14)).reservations = configured.reservations ∧
    (writeBack configured cpu (stateAt 14)).power = true ∧
    (writeBack configured cpu (stateAt 14)).generation = 0 := by
  refine ⟨?_, rfl, rfl, ?_, rfl, rfl⟩
  · intro other different
    exact updateHart_other _ _ _ _ different
  · change updateHart (fun _ : CPU => none) cpu none = _
    exact updateHart_self _ _

theorem global_views : (writeBack configured cpu (stateAt 14)).views = configured.views := by
  change updateHart (fun _ : CPU => 0) cpu 0 = _
  exact updateHart_self _ _

/-- The configured thread pointer denotes the selected actual machine hart. -/
theorem tp_cpu : entry .x4 = BitVec.ofNat 64 cpu.val := rfl

theorem hart_result : MycpuBare.HartResult entry (stateAt 14).registers cpu := by
  refine ⟨result, ?_⟩
  rw [values.2.2.2.1]
  rfl

end Xv6.Kernel.MycpuBareWitness
