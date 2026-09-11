import MachCSL.Logic.DeadThreadSpec
import MachCSL.Logic.PowerGhostProofs
import Iris.ProgramLogic.Lifting

namespace MachCSL.Logic.DeadThread
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Machine

@[simp] theorem threadGeneration_hart (generation : Nat) (cpu : CPU) (program : SailM Unit) :
    threadGeneration (.hart generation cpu program) = some generation := rfl
@[simp] theorem threadGeneration_uart (generation : Nat) :
    threadGeneration (.uart generation) = some generation := rfl
@[simp] theorem threadGeneration_disk (generation : Nat) :
    threadGeneration (.disk generation) = some generation := rfl
@[simp] theorem threadGeneration_plic (generation : Nat) :
    threadGeneration (.plic generation) = some generation := rfl
@[simp] theorem threadGeneration_power : threadGeneration .power = none := rfl

/-- Actual dead arms are always reducible, including a dead hart's error program. -/
theorem dead_step [Platform] (image : BootImage) (e : Expr) (generation : Nat) (g : State)
    (tag : threadGeneration e = some generation) (dead : ¬ ThreadLive g generation) :
    Step image e g [] e g [] := by
  cases e with
  | hart gen cpu program =>
    cases Option.some.inj tag
    exact .hartDead _ _ _ _ dead
  | uart gen =>
    cases Option.some.inj tag
    exact .uartDead _ _ dead
  | disk gen =>
    cases Option.some.inj tag
    exact .diskDead _ _ dead
  | plic gen =>
    cases Option.some.inj tag
    exact .plicDead _ _ dead
  | power => cases tag

/-- The live arms are impossible; every actual successor is the silent self-loop. -/
theorem dead_step_unique [Platform] (image : BootImage) (e : Expr) (generation : Nat) (g : State)
    (tag : threadGeneration e = some generation) (dead : ¬ ThreadLive g generation)
    (events : List Observation) (e' : Expr) (g' : State) (forks : List Expr)
    (step : Step image e g events e' g' forks) :
    e' = e ∧ g' = g ∧ forks = [] ∧ events = [] := by
  cases step <;> simp only [threadGeneration, Option.some.injEq] at tag
  all_goals cases tag
  all_goals first | contradiction | exact ⟨rfl, rfl, rfl, rfl⟩

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

/-- The strict death bound comes from the actual fixed authority, not a pure premise about a chosen state. -/
theorem stateInterp_dead (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (g : State) (steps : Nat) (future : List Observation) (threads generation : Nat) :
    iprop(⊢ MachineInterp.stateInterp capacity fixed whole g steps future threads -∗
      PowerGhost.genDead capacity.power fixed.generation generation -∗ ⌜generation < g.generation⌝) := by
  unfold MachineInterp.stateInterp MachineInterp.powerInterp PowerGhost.counterInterp
    MachineInterp.FixedNames.power
  iintro ⟨⟨⟨Hg, _⟩, _, _⟩, _⟩ Hdead
  iapply PowerGhost.gen_dead_valid capacity.power fixed.generation g.generation generation $$ Hg Hdead

/-- Source `RiscvExec.wp_dead`, for every postcondition of the actual empty value type. -/
theorem wp_dead [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (e : Expr) (generation : Nat) (post : Empty → IProp GF)
    (tag : threadGeneration e = some generation) :
    iprop(PowerGhost.genDead capacity.power fixed.generation generation ⊢
      threadWP capacity image fixed whole e post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold threadWP
  iintro #Hdead
  iloeb as IH
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  ihave %older := stateInterp_dead capacity fixed whole g ns (events ++ future) nt generation $$ Hstate Hdead
  have dead : ¬ ThreadLive g generation := by intro live; have := live.2; omega
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  isplit
  · ipureintro
    exact ⟨[], e, g, [], dead_step image e generation g tag dead⟩
  · iintro !> %e' %g' %forks %step _
    obtain ⟨rfl, rfl, rfl, rfl⟩ := dead_step_unique image e generation g tag dead events e' g' forks step
    imod Hback
    imodintro
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
    iframe Hstate
    isplit
    · iexact IH
    · iapply BigSepL.bigSepL_nil.mpr
      itrivial

theorem wp_dead_hart [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (cpu : CPU) (program : SailM Unit) (post : Empty → IProp GF) :
    iprop(PowerGhost.genDead capacity.power fixed.generation generation ⊢
      threadWP capacity image fixed whole (.hart generation cpu program) post) :=
  wp_dead capacity image fixed whole _ generation post rfl

theorem wp_dead_uart [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (post : Empty → IProp GF) :
    iprop(PowerGhost.genDead capacity.power fixed.generation generation ⊢
      threadWP capacity image fixed whole (.uart generation) post) :=
  wp_dead capacity image fixed whole _ generation post rfl

theorem wp_dead_disk [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (post : Empty → IProp GF) :
    iprop(PowerGhost.genDead capacity.power fixed.generation generation ⊢
      threadWP capacity image fixed whole (.disk generation) post) :=
  wp_dead capacity image fixed whole _ generation post rfl

theorem wp_dead_plic [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (post : Empty → IProp GF) :
    iprop(PowerGhost.genDead capacity.power fixed.generation generation ⊢
      threadWP capacity image fixed whole (.plic generation) post) :=
  wp_dead capacity image fixed whole _ generation post rfl

theorem deadThreadSpec [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : DeadThreadSpec capacity :=
  ⟨wp_dead capacity⟩

end MachCSL.Logic.DeadThread
