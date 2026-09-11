import Xv6.Kernel.MycpuKptEntryProofs

namespace Xv6.Kernel.MycpuKptEntry
open Iris

/-- Every entry/restoration resource rule is implemented from the actual
native source components; no caller-supplied component proof is required. -/
theorem nativeSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity where
  save_area := save_area capacity
  open_entry := open_entry capacity
  close_entry := close_entry capacity
  certificate := certificate capacity

theorem registrySpec {hlc : HasLC} [InvGS_gen hlc MachCSL.Logic.KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.MycpuKptEntry
