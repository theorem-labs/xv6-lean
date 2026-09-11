import Xv6.Kernel.MycpuRegisterSequenceDefs

namespace Xv6.Kernel.MycpuRegisterSequence
open MachCSL.Machine

structure Spec : Prop where
  abi : ∀ entry, CalleeSaved.Preserved entry (returned entry)
  result : ∀ entry, returned entry .x10 = MycpuScalar.mycpuRet (entry .x4)
  return_address : ∀ entry, returned entry .nextPC = MycpuReturn.retPC (entry .x1)
  saved_ra : ∀ entry, returned entry .x1 = entry .x1

end Xv6.Kernel.MycpuRegisterSequence
