import MachCSL.Logic.MachineAdequacyDefs
import MachCSL.Logic.StateAllocationLink
import MachCSL.Logic.PowerWPProofs
import Iris.ProgramLogic.Adequacy

namespace MachCSL.Logic.MachineAdequacy
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.PrimStep MachCSL.Machine
open Language.Notation

variable {GF : BundledGFunctors} [Platform] (capacity : MachineInterp.Capacity GF)

/-- The initializer can ignore its affine disk fragments when the boot
handler follows just from the shared observation invariant. -/
theorem initializer_of_handler (image : BootImage) (initial : State) (diskBytes : Nat)
    (template : Era.Record) (N : Namespace)
    (handler : ∀ [InvGS GF] (fixed : MachineInterp.FixedNames) (whole : List Observation),
      iprop(⊢ ObservationInvariant.trivial capacity.power N fixed.observations -∗
        PowerWP.bootHandler capacity image fixed whole template)) :
    BootInitializer capacity image initial diskBytes template N := by
  intro native fixed whole _
  letI := native
  iintro _ Hobs
  imodintro
  iapply handler fixed whole $$ Hobs

/-- Strong native adequacy over the actual nonempty initial pool `[power]`.
Native invariant allocation and its step credit are performed by the Iris
soundness theorem; application allocation uses that very same world. -/
theorem not_stuck [InvGpreS GF] (image : BootImage) (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0) (diskBytes : Nat)
    (template : Era.Record) (N : Namespace)
    (boot : BootInitializer capacity image initial diskBytes template N)
    (n : Nat) (events : List Observation) (threads : List Expr) (finalState : State)
    (steps : PoolSteps image n ([.power], initial) events (threads, finalState)) :
    letI := language image
    (∀ thread ∈ threads, NotStuck (thread, finalState)) ∧ ObservationsOK events finalState := by
  letI := language image
  apply wp_strong_adequacy_gen (GF := GF) (hlc := .hasLC) .NotStuck [.power] initial
    n events threads finalState _ (fun _ => 0) (Hsteps := steps)
  intro native
  letI := native
  imod MachineInterp.initial_off_alloc capacity (Disk.diskSpec _) initial off zero diskBytes [] events
    (observations_init initial off zero) with ⟨%fixed, %size, Hstate, Hdisk, Hobs⟩
  have allocTrace : iprop(⊢ PowerGhost.obsFrag capacity.power fixed.observations [] -∗
      True ={⊤}=∗ ObservationInvariant.trivial capacity.power N fixed.observations) :=
    ObservationInvariant.allocate capacity.power N ⊤ fixed.observations (fun _ => iprop(True)) []
  imod allocTrace $$ Hobs [] with #Hobs
  · itrivial
  imod boot fixed events size $$ Hdisk Hobs with Hboot
  ihave Hwp := PowerWP.wp_power capacity image fixed events template N (fun _ => iprop(True)) $$ Hobs Hboot
  iexists (MachineInterp.stateInterp capacity fixed events), [(fun _ => iprop(True))],
    (fun _ => iprop(True)), (MachineInterp.irisGS capacity image fixed events).stateInterp_mono
  dsimp only
  imodintro
  isplitl [Hstate]
  · isimp only [MachineInterp.stateInterp, List.nil_append] at Hstate
    unfold MachineInterp.stateInterp
    iexact Hstate
  isplitl [Hwp]
  · isplitl [Hwp]
    · iunfold DeadThread.threadWP at Hwp
      iexact Hwp
    · iapply BigSepL2.bigSepL2_nil
      itrivial
  iintro %original %forked %_ %_ %safe Hstate _ _
  iunfold MachineInterp.stateInterp at Hstate
  icases Hstate with ⟨_, Htrace⟩
  iunfold PowerGhost.obsInterp at Htrace
  icases Htrace with ⟨%history, %total, %wf, _⟩
  have same : history = events := by simpa using total
  subst history
  iapply fupd_mask_intro_discard (by simp)
  ipureintro
  exact ⟨fun thread member => safe thread rfl member, wf⟩

/-- Conditional safety for every finite observed schedule, with actual
machine successors rather than a vacuous postcondition on nonexistent values. -/
theorem safe [InvGpreS GF] (image : BootImage) (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0) (diskBytes : Nat)
    (template : Era.Record) (N : Namespace)
    (boot : BootInitializer capacity image initial diskBytes template N)
    (n : Nat) (events : List Observation) (threads : List Expr) (finalState : State)
    (steps : PoolSteps image n ([.power], initial) events (threads, finalState)) :
    SafeConfiguration image threads finalState events := by
  letI := language image
  obtain ⟨safe, wf⟩ := not_stuck capacity image initial off zero diskBytes template N boot
    n events threads finalState steps
  refine ⟨?_, wf⟩
  intro thread member
  rcases safe thread member with value | step
  · change (none : Option Empty).isSome at value
    contradiction
  · exact step

end MachCSL.Logic.MachineAdequacy
