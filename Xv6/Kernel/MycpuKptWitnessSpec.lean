import Xv6.Kernel.MycpuKptWitnessDefs

namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform

/-- Concrete obligations only. No supplied execution equation or joint resource
inhabitation premise is part of the eventual public witness theorem. -/
structure Spec : Prop where
  cached_image : cachedImage = image
  initial_eq : stateAt 0 = initial
  table_words : ∀ (page : Fin 3) (slot : Fin 512),
    readBytes image (BitVec.ofNat 64 (rootBase + page.val * 4096 + slot.val * 8)) 8 =
      some (tableWord page.val slot.val)
  image_outside : ∀ a, ¬tableRange a → image a = MycpuBareWitness.image a
  scratch_initial : readBytes initial.memory (MycpuBare.raSlot entry) 8 = some 0 ∧
    readBytes initial.memory (MycpuBare.s0Slot entry) 8 = some 0
  checked : ∀ i : Fin 14,
    run cachedImage cpu 4 (cycle false) (stateAt i.val) = some (stateAt (i.val+1))
  cycles : Cycles 14 initial (stateAt 14)
  operational : NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
    (.pure ()) initial (.pure ()) (stateAt 14)
  result : Result (stateAt 14).registers
  values : readBytes (stateAt 14).memory (MycpuBare.raSlot entry) 8 = some (entry .x1) ∧
    readBytes (stateAt 14).memory (MycpuBare.s0Slot entry) 8 = some (entry .x8) ∧
    (stateAt 14).log.length = 2 ∧ (stateAt 14).registers .minstret = 14#64 ∧
    (stateAt 14).registers .mcycle = 0#64 ∧ (stateAt 14).registers .mtime = 0#64
  code : ∀ j : Fin 34,
    (stateAt 14).memory (BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int))) =
      MycpuBareWitness.image (BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int)))
  tables_preserved : ∀ a, tableRange a → (stateAt 14).memory a = image a
  outside_stores : ∀ a, ¬Footprint (MycpuBare.raSlot entry) 8 a →
    ¬Footprint (MycpuBare.s0Slot entry) 8 a → (stateAt 14).memory a = image a
  global_frame : (∀ other, other ≠ cpu → finalState.registers other = configured.registers other) ∧
    finalState.devices = configured.devices ∧ finalState.image = image ∧
    finalState.reservations = configured.reservations ∧ finalState.views = configured.views ∧
    finalState.power = true ∧ finalState.generation = 0
  invariants : MemoryOK configured ∧ ReservationsOK configured ∧
    MemoryOK finalState ∧ ReservationsOK finalState
  full_pool : ∃ n, 0 < n ∧ PoolSteps Xv6.Machine.bootImage n
    (.power :: powerFork 0, configured) [] (.power :: powerFork 0, finalState)

end Xv6.Kernel.MycpuKptWitness
