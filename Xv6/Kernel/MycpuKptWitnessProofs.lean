import Xv6.Kernel.MycpuKptWitnessFirstCertificates
import Xv6.Kernel.MycpuKptWitnessLastCertificates
import Xv6.Kernel.MycpuKptWitnessAssemblyProofs

namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform

theorem checked (i : Fin 14) :
    run cachedImage cpu 4 (cycle false) (stateAt i.val) = some (stateAt (i.val+1)) := by
  obtain ⟨k,hk⟩ := i
  match k with
  | 0 => exact cycle_0
  | 1 => exact cycle_1
  | 2 => exact cycle_2
  | 3 => exact cycle_3
  | 4 => exact cycle_4
  | 5 => exact cycle_5
  | 6 => exact cycle_6
  | 7 => exact cycle_7
  | 8 => exact cycle_8
  | 9 => exact cycle_9
  | 10 => exact cycle_10
  | 11 => exact cycle_11
  | 12 => exact cycle_12
  | 13 => exact cycle_13
  | _ + 14 => omega

theorem cycles : Cycles 14 initial (stateAt 14) := by
  have all := cycles_from_checks checked 14 0 (by decide)
  simpa only [Nat.zero_add, initial_eq] using all

theorem operational : NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
    (.pure ()) initial (.pure ()) (stateAt 14) := operational_from_cycles cycles

theorem full_pool : ∃ n, 0 < n ∧ PoolSteps Xv6.Machine.bootImage n
    (.power :: powerFork 0, configured) [] (.power :: powerFork 0, finalState) :=
  full_pool_from_operational operational

theorem invariants : MemoryOK configured ∧ ReservationsOK configured ∧
    MemoryOK finalState ∧ ReservationsOK finalState :=
  ⟨configured_memory_ok, configured_reservations_ok, final_memory_ok operational⟩

/-- The closed configured witness has no successful-run or native-resource premise. -/
theorem actual : Spec where
  cached_image := cached_image
  initial_eq := initial_eq
  table_words := table_words
  image_outside := image_outside
  scratch_initial := scratch_initial
  checked := checked
  cycles := cycles
  operational := operational
  result := result
  values := values
  code := code
  tables_preserved := tables_preserved
  outside_stores := outside_stores
  global_frame := global_frame
  invariants := invariants
  full_pool := full_pool

end Xv6.Kernel.MycpuKptWitness
