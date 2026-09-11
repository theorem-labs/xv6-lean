import Xv6.Kernel.PushOffStackAuxDefs

namespace Xv6.Kernel.PushOffStack.Bare
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
abbrev patch := MycpuBareSource.patch

def memoryShares (s : Shares) : SupervisorBareFetch.Shares :=
  ⟨⟨.own 1,s.privilege,.own 1⟩,⟨s.pma,.own 1,.own 1,s.htif⟩⟩
def transformShares (s : Shares) : SupervisorAddress.Shares := ⟨.own 1,s.privilege,s.environment,.own 1⟩
def operands (s : Shares) (slot : Slot) : RegisterFootprint.Footprint :=
  [(.menvcfg,s.environment),(.x2,.own 1),(register slot,.own 1)]

end Xv6.Kernel.PushOffStack.Bare
