import MachCSL.Logic.StateTransitionProofs
import MachCSL.Logic.StateAllocationLink

namespace MachCSL.Logic.MachineInterp
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Both observation halves authorize this update. The whole future trace is
retained and the actual power-off event is removed from its remaining suffix. -/
theorem power_off_observed [Platform] (names : FixedNames) (image : BootImage)
    (g : State) (on : g.power = true) (whole history future : List Observation) (steps threads : Nat) :
    iprop(⊢ stateInterp capacity names whole g steps ([.powerOff] ++ future) threads -∗
      PowerGhost.obsFrag capacity.power names.observations history ==∗
      stateInterp capacity names whole (powerOff g) (steps + 1) future threads ∗
      PowerGhost.obsFrag capacity.power names.observations (history ++ [.powerOff]) ∗
      PowerGhost.genDead capacity.power names.generation g.generation) := by
  exact observed_step capacity image .power .power g (powerOff g) [.powerOff] []
    (.power _ _ _ _ (.off on)) names whole history future steps threads
    (PowerGhost.genDead capacity.power names.generation g.generation) (power_off capacity names g on)

/-- The actual eleven forked workers receive the returned certificate and
machine ownership through the caller's subsequent WP construction. -/
theorem power_on_observed [Platform] (names : FixedNames) (image : BootImage)
    (g g' : State) (off : g.power = false) (shape : BootShape image g g')
    (memory : Tso.AddressMap MachCSL.Memory.Byte)
    (rep : MachCSL.Memory.FiniteMap.decode memory = g'.memory) (template : Era.Record)
    (whole history future : List Observation) (steps threads : Nat) :
    iprop(⊢ stateInterp capacity names whole g steps ([.powerOn] ++ future) threads -∗
      PowerGhost.obsFrag capacity.power names.observations history ==∗
      stateInterp capacity names whole g' (steps + 1) future (threads + 11) ∗
      PowerGhost.obsFrag capacity.power names.observations (history ++ [.powerOn]) ∗
      ∃ era : Era.Record, ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
        generationCertificate capacity names g.generation era ∗
        Era.bootClients capacity.era era memory g' names.diskSize) := by
  let clients : IProp GF := iprop(∃ era : Era.Record,
    ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
    generationCertificate capacity names g.generation era ∗
    Era.bootClients capacity.era era memory g' names.diskSize)
  have update : iprop(powerInterp capacity names g ⊢ |==> (powerInterp capacity names g' ∗ clients)) := by
    iintro Hp
    imod power_on capacity (Era.eraSpec _ (Era.contracts _)) names image g g' off shape memory rep template
      $$ Hp with ⟨%era, %same, Hp, Hcert, Hclients⟩
    imodintro
    iframe Hp
    unfold clients
    iexists era
    iframe
    ipureintro
    exact same
  have result := observed_step capacity image .power .power g g' [.powerOn] (powerFork g.generation)
    (.power _ _ _ _ (.on off g' shape)) names whole history future steps threads clients update
  simpa only [powerFork_length] using result

theorem nativeStateTransitionSpec : StateTransitionSpec Invariant.machineCapacity :=
  stateTransitionSpec Invariant.machineCapacity

end MachCSL.Logic.MachineInterp
