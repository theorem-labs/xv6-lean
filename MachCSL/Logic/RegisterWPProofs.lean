import MachCSL.Logic.RegisterWPSpec
import MachCSL.Logic.EraStateLink
import MachCSL.Logic.DeadThreadProofs

namespace MachCSL.Logic.RegisterWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Machine

theorem writeBack_focus (g : State) (cpu : CPU) : writeBack g cpu (focus g cpu) = g := by
  have same {α : Type} (f : CPU → α) : updateHart f cpu (f cpu) = f := by
    funext other
    by_cases h : other = cpu <;> simp [updateHart, h]
  simp only [writeBack, focus, same]

theorem read_step [Platform] (image : BootImage) (g : State) (generation : Nat) (cpu : CPU)
    (r : Register) (k : RegisterType r → SailM Unit) (live : ThreadLive g generation) :
    Step image (.hart generation cpu (.impure (.readReg r) k)) g []
      (.hart generation cpu (k (g.registers cpu r))) g [] := by
  apply Step.hartLive _ _ _ _ _ _ live
  exact ⟨focus g cpu, ⟨rfl, rfl⟩, (writeBack_focus g cpu).symm⟩

theorem read_step_unique [Platform] (image : BootImage) (g : State) (generation : Nat) (cpu : CPU)
    (r : Register) (k : RegisterType r → SailM Unit) (live : ThreadLive g generation)
    (events : List Observation) (e' : Expr) (g' : State) (forks : List Expr)
    (step : Step image (.hart generation cpu (.impure (.readReg r) k)) g events e' g' forks) :
    e' = .hart generation cpu (k (g.registers cpu r)) ∧ g' = g ∧ forks = [] ∧ events = [] := by
  cases step with
  | hartDead _ _ _ _ dead => exact False.elim (dead live)
  | hartLive _ _ _ m' _ _ _ h =>
    obtain ⟨after, ⟨hm, hs⟩, hg⟩ := h
    subst after
    subst m'
    exact ⟨rfl, hg.trans (writeBack_focus g cpu), rfl, rfl⟩

theorem write_step [Platform] (image : BootImage) (g : State) (generation : Nat) (cpu : CPU)
    (r : Register) (value : RegisterType r) (k : Unit → SailM Unit) (live : ThreadLive g generation) :
    Step image (.hart generation cpu (.impure (.writeReg r value) k)) g []
      (.hart generation cpu (k ())) (EraState.writeRegister g cpu r value) [] := by
  apply Step.hartLive _ _ _ _ _ _ live
  exact ⟨(focus g cpu).setReg r value, ⟨rfl, rfl⟩, (EraState.writeBack_register g cpu r value).symm⟩

theorem write_step_unique [Platform] (image : BootImage) (g : State) (generation : Nat) (cpu : CPU)
    (r : Register) (value : RegisterType r) (k : Unit → SailM Unit) (live : ThreadLive g generation)
    (events : List Observation) (e' : Expr) (g' : State) (forks : List Expr)
    (step : Step image (.hart generation cpu (.impure (.writeReg r value) k)) g events e' g' forks) :
    e' = .hart generation cpu (k ()) ∧ g' = EraState.writeRegister g cpu r value ∧ forks = [] ∧ events = [] := by
  cases step with
  | hartDead _ _ _ _ dead => exact False.elim (dead live)
  | hartLive _ _ _ m' _ _ _ h =>
    obtain ⟨after, ⟨hm, hs⟩, hg⟩ := h
    subst after
    subst m'
    exact ⟨rfl, hg.trans (EraState.writeBack_register g cpu r value), rfl, rfl⟩

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

theorem power_dead (fixed : MachineInterp.FixedNames) (g : State) (generation : Nat)
    (older : generation < g.generation) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      PowerGhost.genDead capacity.power fixed.generation generation) := by
  unfold MachineInterp.powerInterp PowerGhost.counterInterp MachineInterp.FixedNames.power
  iintro ⟨⟨Hg, _⟩, _, _⟩
  ihave Hb := PowerGhost.gen_born capacity.power fixed.generation g.generation $$ Hg
  unfold PowerGhost.genDead
  iapply PowerGhost.gen_born_le capacity.power fixed.generation g.generation (generation + 1) (by omega) $$ Hb


theorem wp_read [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (r : Register) (dq : DFrac)
    (value : RegisterType r) (k : RegisterType r → SailM Unit) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      Registers.regPointsto capacity.era.registers (era.registers cpu) r dq value -∗
      ▷ (Registers.regPointsto capacity.era.registers (era.registers cpu) r dq value -∗
        threadWP capacity image fixed whole (.hart generation cpu (k value)) post) -∗
      threadWP capacity image fixed whole (.hart generation cpu (.impure (.readReg r) k)) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold threadWP DeadThread.threadWP
  iintro #Hcert Hvalue Hcontinue
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS]
  iunfold MachineInterp.stateInterp at Hstate
  ihave ⟨Hp, Ho⟩ := Hstate
  ihave %cases := MachineInterp.generation_cases capacity fixed g generation era $$ Hp Hcert
  rcases cases with older | live
  · ihave #Hdead := power_dead capacity fixed g generation older $$ Hp
    have dead : ¬ ThreadLive g generation := by intro live; have := live.2; omega
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, g, [], DeadThread.dead_step image _ generation g rfl dead⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨rfl, rfl, rfl, rfl⟩ := DeadThread.dead_step_unique image _ generation g rfl dead events e' g' forks step
      imod Hback
      imodintro
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · have tail := DeadThread.wp_dead capacity image fixed whole (.hart generation cpu (.impure (.readReg r) k)) generation post rfl
        unfold DeadThread.threadWP at tail
        iapply tail $$ Hdead
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
  · ihave %read := MachineInterp.power_read_register capacity fixed g generation era live cpu r dq value $$ Hp Hcert Hvalue
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, g, [], read_step image g generation cpu r k live⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨rfl, rfl, rfl, rfl⟩ := read_step_unique image g generation cpu r k live events e' g' forks step
      imod Hback
      imodintro
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · rw [read]
        iapply Hcontinue $$ Hvalue
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial

theorem wp_write [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (r : Register)
    (old value : RegisterType r) (k : Unit → SailM Unit) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      Registers.regPointsto capacity.era.registers (era.registers cpu) r (.own 1) old -∗
      ▷ (Registers.regPointsto capacity.era.registers (era.registers cpu) r (.own 1) value -∗
        threadWP capacity image fixed whole (.hart generation cpu (k ())) post) -∗
      threadWP capacity image fixed whole (.hart generation cpu (.impure (.writeReg r value) k)) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold threadWP DeadThread.threadWP
  iintro #Hcert Hvalue Hcontinue
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS]
  iunfold MachineInterp.stateInterp at Hstate
  ihave ⟨Hp, Ho⟩ := Hstate
  ihave %cases := MachineInterp.generation_cases capacity fixed g generation era $$ Hp Hcert
  rcases cases with older | live
  · ihave #Hdead := power_dead capacity fixed g generation older $$ Hp
    have dead : ¬ ThreadLive g generation := by intro live; have := live.2; omega
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, g, [], DeadThread.dead_step image _ generation g rfl dead⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨rfl, rfl, rfl, rfl⟩ := DeadThread.dead_step_unique image _ generation g rfl dead events e' g' forks step
      imod Hback
      imodintro
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · have tail := DeadThread.wp_dead capacity image fixed whole (.hart generation cpu (.impure (.writeReg r value) k)) generation post rfl
        unfold DeadThread.threadWP at tail
        iapply tail $$ Hdead
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
  ·
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, EraState.writeRegister g cpu r value, [], write_step image g generation cpu r value k live⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨rfl, rfl, rfl, rfl⟩ := write_step_unique image g generation cpu r value k live events e' g' forks step
      imod MachineInterp.power_write_register capacity fixed g generation era live cpu r old value $$ Hp Hcert Hvalue with ⟨Hp, Hvalue⟩
      simp only [List.nil_append]
      ihave Ho := PowerGhost.obs_interp_silent capacity.power image _ _ g _ []
        (write_step image g generation cpu r value k live) fixed.observations whole future $$ Ho
      imod Hback
      imodintro
      simp only [List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · iapply Hcontinue $$ Hvalue
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial


theorem wp_read_any [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (r : Register) (k : RegisterType r → SailM Unit) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      ▷ (∀ value : RegisterType r,
        threadWP capacity image fixed whole (.hart generation cpu (k value)) post) -∗
      threadWP capacity image fixed whole (.hart generation cpu (.impure (.readReg r) k)) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold threadWP DeadThread.threadWP
  iintro #Hcert Hcontinue
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS]
  iunfold MachineInterp.stateInterp at Hstate
  ihave ⟨Hp, Ho⟩ := Hstate
  ihave %cases := MachineInterp.generation_cases capacity fixed g generation era $$ Hp Hcert
  rcases cases with older | live
  · ihave #Hdead := power_dead capacity fixed g generation older $$ Hp
    have dead : ¬ ThreadLive g generation := by intro live; have := live.2; omega
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, g, [], DeadThread.dead_step image _ generation g rfl dead⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨rfl, rfl, rfl, rfl⟩ := DeadThread.dead_step_unique image _ generation g rfl dead events e' g' forks step
      imod Hback
      imodintro
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · have tail := DeadThread.wp_dead capacity image fixed whole (.hart generation cpu (.impure (.readReg r) k)) generation post rfl
        unfold DeadThread.threadWP at tail
        iapply tail $$ Hdead
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
  ·
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, g, [], read_step image g generation cpu r k live⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨rfl, rfl, rfl, rfl⟩ := read_step_unique image g generation cpu r k live events e' g' forks step
      imod Hback
      imodintro
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · iapply Hcontinue
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial

theorem registerWPSpec [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : RegisterWPSpec capacity :=
  ⟨wp_read capacity, wp_write capacity, wp_read_any capacity⟩

end MachCSL.Logic.RegisterWP
