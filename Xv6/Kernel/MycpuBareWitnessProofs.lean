import Xv6.Kernel.MycpuBareWitnessFirstCertificates
import Xv6.Kernel.MycpuBareWitnessLastCertificates
import Xv6.Kernel.MycpuBareWitnessAssemblyProofs

namespace Xv6.Kernel.MycpuBareWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform

theorem checked (i : Fin 14) :
    run 4 (cycle false) (stateAt i.val) = some (stateAt (i.val+1)) := by
  obtain ⟨k, hk⟩ := i
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

theorem pool : ∃ n, PoolSteps Xv6.Machine.bootImage n
    ([.hart 0 cpu (.pure ())], configured) []
    ([.hart 0 cpu (.pure ())], writeBack configured cpu (stateAt 14)) :=
  pool_from_operational operational

theorem pool_positive : ∃ n, 0 < n ∧ PoolSteps Xv6.Machine.bootImage n
    ([.hart 0 cpu (.pure ())], configured) []
    ([.hart 0 cpu (.pure ())], writeBack configured cpu (stateAt 14)) :=
  pool_positive_from_operational operational

theorem final_invariants : MemoryOK (writeBack configured cpu (stateAt 14)) ∧
    ReservationsOK (writeBack configured cpu (stateAt 14)) :=
  final_memory_ok operational

/-- All public operational witness fields have closed, kernel-checked proofs. -/
theorem actual : Spec :=
  ⟨entry_config, cached_image, cycles, operational, result, values, code, pool⟩

end Xv6.Kernel.MycpuBareWitness
