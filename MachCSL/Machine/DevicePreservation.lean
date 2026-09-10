import MachCSL.Machine.State
import MachCSL.Devices.FabricProofs

namespace MachCSL.Machine
open Memory

/-- A device projection preserved by every bus transaction is preserved by
every hart event, including blocked memory effects and cycle restart. -/
theorem node_device_projection [Platform] (bus : Bus Device) (project : Device → α)
    (readPreserves : ∀ d d' pa n w, bus.read d pa n = some (w, d') → project d' = project d)
    (writePreserves : ∀ d d' pa n w, bus.write d pa n w = some d' → project d' = project d)
    (others : PhysicalAddress → Prop) (hart : Agent) (image : ByteMap 64)
    (s s' : LocalState Device) (m m' : SailM Unit)
    (step : NodeStep bus others hart image s m m' s') : project s'.devices = project s.devices := by
  cases m with
  | pure value =>
    obtain ⟨tick, _, rfl⟩ := step
    rfl
  | impure event k =>
    cases event <;> simp only [NodeStep] at step
    all_goals first
      | solve | contradiction
      | solve | obtain ⟨_, rfl⟩ := step; rfl
      | solve | obtain ⟨_, _, rfl⟩ := step; rfl
      | skip
    case readMem n req =>
      split at step
      · obtain ⟨w, d, read, _, rfl⟩ := step
        exact readPreserves _ _ _ _ _ read
      · rcases step with ⟨_, view, w, _, _, _, _, rfl⟩ | ⟨_, blocked | acquired⟩
        · rfl
        · obtain ⟨_, _, rfl⟩ := blocked
          rfl
        · obtain ⟨_, w, _, _, rfl⟩ := acquired
          rfl
    case writeMem n req =>
      split at step
      · contradiction
      · split at step
        · obtain ⟨d, write, _, rfl⟩ := step
          exact writePreserves _ _ _ _ _ write
        · rcases step with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

theorem hart_wire [Platform] (g g' : State) (cpu : CPU) (m m' : SailM Unit)
    (step : HartStep g cpu m m' g') : g'.devices.uart.wire = g.devices.uart.wire := by
  obtain ⟨after, node, rfl⟩ := step
  exact node_device_projection Devices.bus (fun d => d.uart.wire)
    Devices.read_wire Devices.write_wire _ _ _ _ _ _ _ node

theorem hart_disk [Platform] (g g' : State) (cpu : CPU) (m m' : SailM Unit)
    (step : HartStep g cpu m m' g') : g'.devices.virtio.v_disk = g.devices.virtio.v_disk := by
  obtain ⟨after, node, rfl⟩ := step
  exact node_device_projection Devices.bus (fun d => d.virtio.v_disk)
    Devices.read_disk Devices.write_disk _ _ _ _ _ _ _ node

end MachCSL.Machine
