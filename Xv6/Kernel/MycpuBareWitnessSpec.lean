import Xv6.Kernel.MycpuBareWitnessDefs

namespace Xv6.Kernel.MycpuBareWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform

structure Spec : Prop where
  entry_config : MycpuBare.EntryConfig entry
  cached_image : cachedImage = image
  cycles : Cycles 14 initial (stateAt 14)
  operational : NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
    (.pure ()) initial (.pure ()) (stateAt 14)
  result : MycpuBare.Result entry (stateAt 14).registers
  values : (stateAt 14).registers .x1 = entry .x1 ∧
    (stateAt 14).registers .x8 = entry .x8 ∧
    (stateAt 14).registers .x2 = entry .x2 ∧
    (stateAt 14).registers .x10 = 0x80012568#64 ∧
    readBytes (stateAt 14).memory (MycpuBare.raSlot entry) 8 = some (entry .x1) ∧
    readBytes (stateAt 14).memory (MycpuBare.s0Slot entry) 8 = some (entry .x8) ∧
    (stateAt 14).log.length = 2
  code : ∀ j : Fin 34,
    (stateAt 14).memory (BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int))) =
      image (BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int)))
  pool : ∃ n, PoolSteps Xv6.Machine.bootImage n
    ([.hart 0 cpu (.pure ())], configured) []
    ([.hart 0 cpu (.pure ())], writeBack configured cpu (stateAt 14))

end Xv6.Kernel.MycpuBareWitness
