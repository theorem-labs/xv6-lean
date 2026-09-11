import MachCSL.Logic.StateInterpDefs

namespace MachCSL.Logic.MachineInterp
open Iris Iris.BI MachCSL.Machine

/-- Trace/state composition only: the caller must prove the actual power/era
resource update. This contract does not assume hardware preservation for free. -/
structure StateTransitionSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  observed : ∀ [Platform] image e e' g g' events forks,
    Step image e g events e' g' forks → ∀ names whole history future steps threads (R : IProp GF),
    iprop(powerInterp capacity names g ⊢ |==> (powerInterp capacity names g' ∗ R)) →
    iprop(⊢ stateInterp capacity names whole g steps (events ++ future) threads -∗
      PowerGhost.obsFrag capacity.power names.observations history ==∗
      stateInterp capacity names whole g' (steps + 1) future (threads + forks.length) ∗
      PowerGhost.obsFrag capacity.power names.observations (history ++ events) ∗ R)
  silent : ∀ [Platform] image e e' g g' forks,
    Step image e g [] e' g' forks → ∀ names whole future steps threads (R : IProp GF),
    iprop(powerInterp capacity names g ⊢ |==> (powerInterp capacity names g' ∗ R)) →
    iprop(stateInterp capacity names whole g steps future threads ⊢ |==>
      (stateInterp capacity names whole g' (steps + 1) future (threads + forks.length) ∗ R))

end MachCSL.Logic.MachineInterp
