import Xv6.Kernel.MycpuActiveDefs
import Xv6.Kernel.MycpuScalarDefs
import Xv6.Kernel.MycpuMemoryDefs
import Xv6.Kernel.MycpuReturnDefs
import MachCSL.Logic.SupervisorRetirementDefs

/-! One nonduplicated register footprint for composing actual mycpu bodies
with fetch, dispatch, retirement and both clocks. No full-cycle theorem here. -/
namespace Xv6.Kernel.MycpuCycleBody
open Iris MachCSL.Machine MachCSL.Logic

structure Shares where
  bare : SupervisorBareFetch.Shares
  misa : DFrac
  enable : DFrac
  delegation : DFrac
  environment : DFrac
  landing : DFrac
  tp : DFrac
  hart : DFrac

def activeShares (s : Shares) : MycpuActive.Shares :=
  ⟨⟨.own 1, s.misa, s.bare⟩, s.enable, s.delegation, s.environment, s.landing⟩

def memoryShares (s : Shares) : MycpuMemory.Shares := ⟨s.bare, s.environment, .own 1, .own 1⟩
def returnShares (s : Shares) : MycpuReturn.Shares :=
  ⟨.own 1, s.bare.translation.privilege, s.environment, s.misa⟩

def footprint (s : Shares) : RegisterFootprint.Footprint :=
  MycpuActive.footprint (activeShares s) ++
  [(.x1, .own 1), (.x2, .own 1), (.x8, .own 1), (.x15, .own 1),
   (.x10, .own 1), (.x4, s.tp)] ++ SupervisorRetirement.retirementFootprint ++
  SupervisorClock.clockFootprint ++ [(.hart_state, s.hart)]

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

end Xv6.Kernel.MycpuCycleBody
