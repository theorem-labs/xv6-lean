import MachCSL.Logic.DeadThreadDefs

namespace MachCSL.Logic.DeadThread
open Iris Iris.BI MachCSL.Machine

structure DeadThreadSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  dead : ∀ image fixed whole e generation post, threadGeneration e = some generation →
    iprop(PowerGhost.genDead capacity.power fixed.generation generation ⊢
      threadWP capacity image fixed whole e post)

end MachCSL.Logic.DeadThread
