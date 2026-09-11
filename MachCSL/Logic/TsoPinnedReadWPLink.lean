import MachCSL.Logic.TsoPinnedReadWPProofs
import MachCSL.Logic.FsBlockGhostLink

namespace MachCSL.Logic.TsoPinnedReadWP
open Iris MachCSL.Machine

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

theorem registrySpec [Platform] [InvGS FsBlockGhost.registry] :
    Spec FsBlockGhost.machineCapacity := actual _

end MachCSL.Logic.TsoPinnedReadWP
