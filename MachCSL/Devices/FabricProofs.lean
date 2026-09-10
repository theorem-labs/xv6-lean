import MachCSL.Devices.Fabric
import MachCSL.Devices.Virtio.Proofs
import MachCSL.Devices.Uart.Proofs

namespace MachCSL.Devices

/-- No CPU MMIO read changes durable disk bytes. -/
theorem read_disk (d d' : State) (pa : Memory.PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) (h : read d pa n = some (word, d')) :
    d'.virtio.v_disk = d.virtio.v_disk := by
  unfold read at h
  dsimp only at h
  split at h
  · split at h
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨b, u⟩, _, _, rfl⟩ := h
      rfl
    · contradiction
  · split at h
    · split at h
      · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨w, p⟩, _, _, rfl⟩ := h
        rfl
      · contradiction
    · split at h
      · split at h
        · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨w, _, _, rfl⟩ := h
          rfl
        · split at h
          · cases h
            rfl
          · contradiction
      · contradiction

/-- MMIO reset commands can discard volatile cache, but preserve durable disk. -/
theorem write_disk (d d' : State) (pa : Memory.PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) (h : write d pa n word = some d') :
    d'.virtio.v_disk = d.virtio.v_disk := by
  unfold write at h
  dsimp only at h
  split at h
  · split at h
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨u, _, rfl⟩ := h
      rfl
    · contradiction
  · split at h
    · split at h
      · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨p, _, rfl⟩ := h
        rfl
      · contradiction
    · split at h
      · split at h
        · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨v, hv, rfl⟩ := h
          exact Virtio.virtio_write_disk _ _ _ _ hv
        · split at h
          · cases h
            rfl
          · contradiction
      · contradiction

/-- MMIO reads cannot transmit a byte on the UART wire. -/
theorem read_wire (d d' : State) (pa : Memory.PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) (h : read d pa n = some (word, d')) :
    d'.uart.wire = d.uart.wire := by
  unfold read at h
  dsimp only at h
  split at h
  · split at h
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨b, u⟩, hu, _, rfl⟩ := h
      exact (Uart.read_fields d.uart _ b u hu).2.2.1
    · contradiction
  · split at h
    · split at h
      · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨w, p⟩, _, _, rfl⟩ := h
        rfl
      · contradiction
    · split at h
      · split at h
        · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨w, _, _, rfl⟩ := h
          rfl
        · split at h
          · cases h
            rfl
          · contradiction
      · contradiction

/-- MMIO writes only queue UART transmission; the device actor emits it later. -/
theorem write_wire (d d' : State) (pa : Memory.PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) (h : write d pa n word = some d') :
    d'.uart.wire = d.uart.wire := by
  unfold write at h
  dsimp only at h
  split at h
  · split at h
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact (Uart.write_traces d.uart _ _ u hu).2
    · contradiction
  · split at h
    · split at h
      · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨p, _, rfl⟩ := h
        rfl
      · contradiction
    · split at h
      · split at h
        · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨v, hv, rfl⟩ := h
          rfl
        · split at h
          · cases h
            rfl
          · contradiction
      · contradiction

end MachCSL.Devices
