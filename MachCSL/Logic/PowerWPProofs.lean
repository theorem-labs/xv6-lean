import MachCSL.Logic.PowerWPSpec
import MachCSL.Logic.ObservationInvariantProofs
import MachCSL.Logic.StateInterpLink
import Iris.ProgramLogic.Lifting

namespace MachCSL.Logic.PowerWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

/-- Moving history is paid by the shared fixed invariant. The actual transition
supplies the trace-shape/wire proof when reconstructing the interpretation. -/
theorem observed [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (e e' : Expr) (g g' : State) (events : List Observation) (forks : List Expr)
    (step : Step image e g events e' g' forks) (N : Namespace) (γ : GName)
    (whole future : List Observation) :
    iprop(⊢ ObservationInvariant.trivial capacity.power N γ -∗
      PowerGhost.obsInterp capacity.power γ whole g (events ++ future) ={⊤}=∗
      PowerGhost.obsInterp capacity.power γ whole g' future) := by
  iintro Hinv Ho
  iunfold PowerGhost.obsInterp at Ho
  icases Ho with ⟨%history, %total, %wf, Ha⟩
  imod ObservationInvariant.trivial_update capacity.power N ⊤ γ history (history ++ events)
    (by intro x hx; exact CoPset.mem_full) $$ Hinv Ha with Ha
  imodintro
  iapply PowerGhost.obs_interp_close capacity.power image e e' g g' events forks history future whole
    step wf total γ $$ Ha

theorem wp_power [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (template : Era.Record) (N : Namespace) (post : Empty → IProp GF) :
    iprop(⊢ ObservationInvariant.trivial capacity.power N fixed.observations -∗
      bootHandler capacity image fixed whole template -∗
      DeadThread.threadWP capacity image fixed whole .power post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold DeadThread.threadWP
  iintro #Hobs Hboot
  iunfold bootHandler at Hboot
  icases Hboot with #Hboot
  iloeb as IH
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS]
  iunfold MachineInterp.stateInterp at Hstate
  icases Hstate with ⟨Hp, Ho⟩
  iapply fupd_mask_intro (E2 := ∅) (by intro x hx; exact CoPset.mem_full)
  iintro Hback
  isplit
  · ipureintro
    obtain ⟨events, next, forks, step⟩ := power_can_step image g
    exact ⟨events, .power, next, forks, step⟩
  · iintro !> %e' %g' %forks %step _
    change Step image .power g events e' g' forks at step
    imod Hback
    imod observed capacity image .power e' g g' events forks step N fixed.observations whole future
      $$ Hobs Ho with Ho
    cases step with
    | power g events next forks transition =>
      cases transition with
      | off on =>
        imod MachineInterp.power_off capacity fixed g on $$ Hp with ⟨Hp, _⟩
        imodintro
        dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
        unfold powerOff
        iframe Hp Ho
        isplit
        · iexact IH
        · iapply BigSepL.bigSepL_nil.mpr
          itrivial
      | on off next shape =>
        let memory := Memory.FiniteMap.encodeAll g'.memory
        have rep : Memory.FiniteMap.decode memory = g'.memory := Memory.FiniteMap.decode_encodeAll _
        imod MachineInterp.power_on capacity (Era.eraSpec _ (Era.contracts _)) fixed image g g'
          off shape memory rep template $$ Hp with ⟨%era, %info, Hp, Hcert, Hclients⟩
        have gen := shape.1
        rw [← gen]
        imod Hboot $$ %g' %era %memory [] [] [] Hcert Hclients with Hforks
        · ipureintro; exact shape.2.2
        · ipureintro; exact rep
        · ipureintro; exact info
        · imodintro
          dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
          iframe Hp Ho
          isplitl []
          · iexact IH
          · iunfold DeadThread.threadWP at Hforks
            iexact Hforks

theorem powerWPSpec [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : PowerWPSpec capacity :=
  ⟨wp_power capacity⟩

end MachCSL.Logic.PowerWP
