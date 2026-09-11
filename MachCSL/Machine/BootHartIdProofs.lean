import MachCSL.Machine.BootUniversalRun

/-! The board's hart identifier survives the actual generated reset program.
This projection ranges over arbitrary preboot register files. -/
namespace MachCSL.Machine.BootHartId
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem projection (before : RegisterFile) (vector hart : BitVec 64) :
    (BootUniversal.result before vector hart).map (fun (_, rs) => rs .mhartid) = some hart := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem run_hartid (bus : Bus Device) (before : RegisterFile) (vector hart : BitVec 64)
    (memory : Memory.ByteMap 64) (devices : Device) (after : ViewState Device)
    (run : Run bus (bootProgram vector hart pmaBoot) ⟨before, memory, devices⟩ () after) :
    after.registers .mhartid = hart := by
  have projected := projection before vector hart
  cases computed : BootUniversal.result before vector hart with
  | none =>
    simp only [computed, Option.map_none] at projected
    contradiction
  | some pair =>
    obtain ⟨u, registers⟩ := pair
    cases u
    have unique := BootUniversal.registerRun_unique bus 10000 _ before registers () () memory devices after computed run
    rw [congrArg ViewState.registers unique.2]
    rw [computed] at projected
    exact Option.some.inj projected

theorem bootFacts_hartid (image : BootImage) (g : State) (facts : BootFacts image g) (cpu : CPU) :
    g.registers cpu .mhartid = BitVec.ofNat 64 cpu.val := by
  obtain ⟨before, after, run, same⟩ := facts.2.2.1 cpu
  rw [same]
  exact run_hartid Devices.bus before image.vector (BitVec.ofNat 64 cpu.val)
    Memory.empty Devices.initial ⟨after, Memory.empty, Devices.initial⟩ run

/-- The identifier selects exactly the two intended CPUs after every boot. -/
theorem bootFacts_selected (image : BootImage) (g : State) (facts : BootFacts image g) (cpu : CPU) :
    (g.registers cpu .mhartid).toNat < 2 ↔ cpu.val < 2 := by
  rw [bootFacts_hartid image g facts cpu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := cpu.isLt
  omega

end MachCSL.Machine.BootHartId
