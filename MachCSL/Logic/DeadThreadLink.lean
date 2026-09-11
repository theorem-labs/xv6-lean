import MachCSL.Logic.DeadThreadProofs
import MachCSL.Logic.InvariantLink

namespace MachCSL.Logic.DeadThread
open Iris Iris.BI MachCSL.Machine

/-- No abstract component-specification premise remains at the current final registry. -/
theorem registryDeadThreadSpec [Platform] (names : Invariant.Names) :
    letI := names.native Invariant.registryCapacity
    DeadThreadSpec Invariant.machineCapacity := by
  letI := names.native Invariant.registryCapacity
  exact deadThreadSpec Invariant.machineCapacity

theorem registry_wp_dead [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (e : Expr) (generation : Nat) (post : Empty → IProp Invariant.registry)
    (tag : threadGeneration e = some generation) :
    letI := names.native Invariant.registryCapacity
    iprop(PowerGhost.genDead Invariant.machineCapacity.power fixed.generation generation ⊢
      threadWP Invariant.machineCapacity image fixed whole e post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_dead Invariant.machineCapacity image fixed whole e generation post tag

end MachCSL.Logic.DeadThread
