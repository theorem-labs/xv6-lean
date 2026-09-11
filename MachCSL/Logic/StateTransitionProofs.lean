import MachCSL.Logic.StateTransitionSpec
import MachCSL.Logic.PowerGhostProofs

namespace MachCSL.Logic.MachineInterp
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem observed_step [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (events forks) (step : Step image e g events e' g' forks)
    (names : FixedNames) (whole history future : List Observation) (steps threads : Nat)
    (R : IProp GF)
    (transition : iprop(powerInterp capacity names g ⊢ |==> (powerInterp capacity names g' ∗ R))) :
    iprop(⊢ stateInterp capacity names whole g steps (events ++ future) threads -∗
      PowerGhost.obsFrag capacity.power names.observations history ==∗
      stateInterp capacity names whole g' (steps + 1) future (threads + forks.length) ∗
      PowerGhost.obsFrag capacity.power names.observations (history ++ events) ∗ R) := by
  unfold stateInterp PowerGhost.obsInterp
  iintro ⟨Hp, %past, %total, %wf, Ho⟩ Hfrag
  ihave %same := PowerGhost.obs_agree capacity.power names.observations past history $$ Ho Hfrag
  subst past
  imod transition $$ Hp with ⟨Hp, HR⟩
  imod PowerGhost.obs_update capacity.power names.observations history (history ++ events)
    $$ Ho Hfrag with ⟨Ho, Hfrag⟩
  imodintro
  iframe
  ipureintro
  exact ⟨by simpa only [List.append_assoc] using total,
    step_observations_ok image e e' g g' events forks history wf step⟩

theorem silent_step [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (forks) (step : Step image e g [] e' g' forks)
    (names : FixedNames) (whole future : List Observation) (steps threads : Nat) (R : IProp GF)
    (transition : iprop(powerInterp capacity names g ⊢ |==> (powerInterp capacity names g' ∗ R))) :
    iprop(stateInterp capacity names whole g steps future threads ⊢ |==>
      (stateInterp capacity names whole g' (steps + 1) future (threads + forks.length) ∗ R)) := by
  unfold stateInterp
  iintro ⟨Hp, Ho⟩
  imod transition $$ Hp with ⟨Hp, HR⟩
  ihave Ho' := PowerGhost.obs_interp_silent capacity.power image e e' g g' forks step
    names.observations whole future $$ Ho
  imodintro
  iframe

theorem stateTransitionSpec : StateTransitionSpec capacity :=
  ⟨observed_step capacity, silent_step capacity⟩

end MachCSL.Logic.MachineInterp
