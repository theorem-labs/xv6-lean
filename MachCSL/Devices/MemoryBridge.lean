import MachCSL.Devices.Virtio.DmaProofs
import MachCSL.Memory.ReadBytes

/-! Shared byte semantics for CPU reads and the DMA implementation. These
bridges discharge Lean representation differences; they do not assert a
cross-prover correspondence with Rocq. -/
namespace MachCSL.Devices.Virtio

theorem assemble_bytes_eq (bytes : List Byte) :
    assemble_bytes bytes = (Memory.assembleBytes bytes : Int) := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih => simp [assemble_bytes, Memory.assembleBytes, ih]

theorem read_bytes_eq (memory : ByteMap) (address : Address) (n : Nat) :
    read_bytes memory address n = Memory.readBytes memory address n := by
  simp only [read_bytes, read_byte_list, Memory.readBytes]
  congr 1
  funext bytes
  rw [assemble_bytes_eq]
  rfl

theorem read_bytes_spec (memory : ByteMap) (address : Address) (n : Nat)
    (word : BitVec (8 * n)) :
    read_bytes memory address n = some word ↔
      ∀ j, j < n → memory (Memory.addressAdd address j) = some (Memory.nthByte word j) := by
  rw [read_bytes_eq]
  exact Memory.readBytes_eq_some_iff memory address n word

end MachCSL.Devices.Virtio
