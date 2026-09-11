import MachCSL.Logic.BarrierWPSpec
import MachCSL.Logic.TsoReadProofs
import MachCSL.Logic.RegisterWPProofs

namespace MachCSL.Logic.BarrierWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Memory MachCSL.Machine

theorem barrierAt_inv (m : SailM α) (kind : barrier_kind) (projected : barrierAt m = some kind) :
    ∃ k, m = .impure (.barrier kind) k ∧ barrierResume m = k () := by
  cases m with
  | pure _ => simp [barrierAt] at projected
  | impure e k =>
    cases e <;> simp only [barrierAt] at projected
    all_goals first | contradiction | skip
    cases Option.some.inj projected
    exact ⟨k, rfl, rfl⟩

theorem afterBarrier_live (g : State) (gen : Nat) (cpu : CPU) (kind : barrier_kind)
    (live : ThreadLive g gen) : ThreadLive (afterBarrier g cpu kind) gen := live

theorem afterBarrier_nondraining (g : State) (cpu : CPU) (kind : barrier_kind)
    (doesNotDrain : fenceDrains kind = false) : afterBarrier g cpu kind = g := by
  have same : updateHart g.views cpu (g.views cpu) = g.views := by
    funext other
    by_cases h : other = cpu <;> simp [updateHart, h]
  simp [afterBarrier, TsoRead.advanceView, fencePost, doesNotDrain, same]

/-- The actual barrier retains every field except the selected CPU's view. -/
theorem afterBarrier_frame (g : State) (cpu : CPU) (kind : barrier_kind) :
    (afterBarrier g cpu kind).registers = g.registers ∧
    (afterBarrier g cpu kind).memory = g.memory ∧
    (afterBarrier g cpu kind).devices = g.devices ∧
    (afterBarrier g cpu kind).generation = g.generation ∧
    (afterBarrier g cpu kind).power = g.power ∧
    (afterBarrier g cpu kind).reservations = g.reservations ∧
    (afterBarrier g cpu kind).image = g.image ∧
    (afterBarrier g cpu kind).log = g.log ∧
    (∀ other, other ≠ cpu → (afterBarrier g cpu kind).views other = g.views other) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro other different
  simp [afterBarrier, TsoRead.advanceView, updateHart, different]

theorem afterBarrier_own (g : State) (cpu : CPU) (kind : barrier_kind)
    (drains : fenceDrains kind = true) :
    ownPub (hartAgent cpu) (afterBarrier g cpu kind).log ≤ (afterBarrier g cpu kind).views cpu := by
  simp [afterBarrier, TsoRead.advanceView, updateHart, drains, fencePost, Nat.le_max_right]

theorem barrier_step [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (kind : barrier_kind) (k : Unit → SailM Unit) (live : ThreadLive g gen) :
    Step image (.hart gen cpu (.impure (.barrier kind) k)) g []
      (.hart gen cpu (k ())) (afterBarrier g cpu kind) [] := by
  apply Step.hartLive _ _ _ _ _ _ live
  exact ⟨{ focus g cpu with view := fencePost (hartAgent cpu) g.log (fenceDrains kind) (g.views cpu) },
    ⟨rfl, rfl⟩, (TsoRead.writeBack_view g cpu _).symm⟩

theorem barrier_step_unique [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (kind : barrier_kind) (k : Unit → SailM Unit) (live : ThreadLive g gen)
    (events : List Observation) (e' : Expr) (g' : State) (forks : List Expr)
    (step : Step image (.hart gen cpu (.impure (.barrier kind) k)) g events e' g' forks) :
    e' = .hart gen cpu (k ()) ∧ g' = afterBarrier g cpu kind ∧ forks = [] ∧ events = [] := by
  cases step with
  | hartDead _ _ _ _ dead => exact False.elim (dead live)
  | hartLive _ _ _ m' _ _ _ h =>
    obtain ⟨after, ⟨hm, hs⟩, hg⟩ := h
    subst after
    subst m'
    exact ⟨rfl, hg.trans (TsoRead.writeBack_view g cpu _), rfl, rfl⟩

variable {GF : BundledGFunctors}

theorem ghostStep_id (capacity : Era.Capacity GF) (era : Era.Record) (P : IProp GF) :
    iprop(⊢ ghostStep capacity era P P) := by
  unfold ghostStep
  iintro %g Hheap Htso HP
  imodintro
  iframe

theorem pubStep_id (capacity : Era.Capacity GF) (era : Era.Record) (cpu : CPU) (P : IProp GF) :
    iprop(⊢ pubStep capacity era cpu P P) := by
  unfold pubStep
  iintro %g _ _ Hheap Htso HP
  imodintro
  iframe

theorem pubStep_of_ghostStep (capacity : Era.Capacity GF) (era : Era.Record) (cpu : CPU)
    (P Q : IProp GF) : iprop(ghostStep capacity era P Q ⊢ pubStep capacity era cpu P Q) := by
  unfold ghostStep pubStep
  iintro Hstep %g _ _ Hheap Htso HP
  iapply Hstep $$ Hheap Htso HP

theorem power_ghost (capacity : MachineInterp.Capacity GF) (fixed : MachineInterp.FixedNames)
    (g : State) (gen : Nat) (era : Era.Record) (cpu : CPU) (kind : barrier_kind)
    (P Q : IProp GF) (live : ThreadLive g gen) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      ghostStep capacity.era era P Q -∗ P ==∗
      MachineInterp.powerInterp capacity fixed (afterBarrier g cpu kind) ∗ Q) := by
  iintro Hp #Hcert Hstep HP
  ihave %ok := TsoRead.power_memoryOK capacity fixed g gen era live $$ Hp Hcert
  imod TsoRead.power_advance capacity fixed g gen era cpu (fencePost (hartAgent cpu) g.log (fenceDrains kind) (g.views cpu)) live
    (fencePost_mono _ _ _ _) (fencePost_le_length _ _ _ _ (ok.2.1 cpu)) $$ Hp Hcert with ⟨Hp, _⟩
  rw [← afterBarrier]
  ihave ⟨Hera, Hclose⟩ := MachineInterp.live_era_access capacity fixed (afterBarrier g cpu kind)
    gen era (afterBarrier_live g gen cpu kind live) $$ Hp Hcert
  iunfold Era.interp at Hera
  ihave ⟨Hr, Hheap, Hd, Hdisk, Htso, Hres, Hvalid⟩ := Hera
  iunfold ghostStep at Hstep
  imod Hstep $$ Hheap Htso HP with ⟨Hheap, Htso, HQ⟩
  imodintro
  isplitr [HQ]
  · iapply Hclose
    unfold Era.interp
    iframe
  · iexact HQ

theorem power_publish (capacity : MachineInterp.Capacity GF) (fixed : MachineInterp.FixedNames)
    (g : State) (gen : Nat) (era : Era.Record) (cpu : CPU) (kind : barrier_kind)
    (P Q : IProp GF) (live : ThreadLive g gen) (drains : fenceDrains kind = true) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      pubStep capacity.era era cpu P Q -∗ P ==∗
      MachineInterp.powerInterp capacity fixed (afterBarrier g cpu kind) ∗ Q) := by
  iintro Hp #Hcert Hstep HP
  ihave %ok := TsoRead.power_memoryOK capacity fixed g gen era live $$ Hp Hcert
  imod TsoRead.power_advance capacity fixed g gen era cpu (fencePost (hartAgent cpu) g.log (fenceDrains kind) (g.views cpu)) live
    (fencePost_mono _ _ _ _) (fencePost_le_length _ _ _ _ (ok.2.1 cpu)) $$ Hp Hcert with ⟨Hp, Hreceipt⟩
  rw [← afterBarrier]
  ihave ⟨Hera, Hclose⟩ := MachineInterp.live_era_access capacity fixed (afterBarrier g cpu kind)
    gen era (afterBarrier_live g gen cpu kind live) $$ Hp Hcert
  iunfold Era.interp at Hera
  ihave ⟨Hr, Hheap, Hd, Hdisk, Htso, Hres, Hvalid⟩ := Hera
  have own := afterBarrier_own g cpu kind drains
  have receipt : (afterBarrier g cpu kind).views cpu =
      fencePost (hartAgent cpu) g.log (fenceDrains kind) (g.views cpu) :=
    TsoRead.advanceView_here g cpu _
  iunfold pubStep at Hstep
  imod Hstep $$ %(afterBarrier g cpu kind) %own [Hreceipt] Hheap Htso HP with ⟨Hheap, Htso, HQ⟩
  · rw [receipt]; iexact Hreceipt
  imodintro
  isplitr [HQ]
  · iapply Hclose
    unfold Era.interp
    iframe
  · iexact HQ

/-- Internal factorization of the two public proofs. Its update argument is
discharged below by the proved heap/TSO framing laws, not exposed as a public
barrier contract or required of a client. -/
private theorem wp_update [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (kind : barrier_kind) (k : Unit → SailM Unit) (C P Q : IProp GF) (post : Empty → IProp GF)
    (update : ∀ g, ThreadLive g gen →
      iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
        MachineInterp.generationCertificate capacity fixed gen era -∗ C -∗ P ==∗
        MachineInterp.powerInterp capacity fixed (afterBarrier g cpu kind) ∗ Q)) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ C -∗ P -∗
      ▷ (Q -∗ threadWP capacity image fixed whole (.hart gen cpu (k ())) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.barrier kind) k)) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold threadWP DeadThread.threadWP
  iintro #Hcert HC HP Hcontinue
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS]
  iunfold MachineInterp.stateInterp at Hstate
  ihave ⟨Hp, Ho⟩ := Hstate
  ihave %cases := MachineInterp.generation_cases capacity fixed g gen era $$ Hp Hcert
  rcases cases with older | live
  · ihave #Hdead := RegisterWP.power_dead capacity fixed g gen older $$ Hp
    have dead : ¬ ThreadLive g gen := by intro live; have := live.2; omega
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, g, [], DeadThread.dead_step image _ gen g rfl dead⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨rfl, rfl, rfl, rfl⟩ := DeadThread.dead_step_unique image _ gen g rfl dead events e' g' forks step
      imod Hback
      imodintro
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · have tail := DeadThread.wp_dead capacity image fixed whole
          (.hart gen cpu (.impure (.barrier kind) k)) gen post rfl
        unfold DeadThread.threadWP at tail
        iapply tail $$ Hdead
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
  · iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, afterBarrier g cpu kind, [], barrier_step image g gen cpu kind k live⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨rfl, rfl, rfl, rfl⟩ := barrier_step_unique image g gen cpu kind k live events e' g' forks step
      imod update g live $$ Hp Hcert HC HP with ⟨Hp, HQ⟩
      simp only [List.nil_append]
      ihave Ho := PowerGhost.obs_interp_silent capacity.power image _ _ g _ []
        (barrier_step image g gen cpu kind k live) fixed.observations whole future $$ Ho
      imod Hback
      imodintro
      simp only [List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · iapply Hcontinue $$ HQ
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial

theorem wp_ghost [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (kind : barrier_kind) (k : Unit → SailM Unit) (P Q : IProp GF) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      ghostStep capacity.era era P Q -∗ P -∗
      ▷ (Q -∗ threadWP capacity image fixed whole (.hart gen cpu (k ())) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.barrier kind) k)) post) :=
  wp_update capacity image fixed whole gen era cpu kind k _ P Q post
    (fun g live => power_ghost capacity fixed g gen era cpu kind P Q live)

theorem wp_publish [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (kind : barrier_kind) (k : Unit → SailM Unit) (P Q : IProp GF) (post : Empty → IProp GF)
    (drains : fenceDrains kind = true) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      pubStep capacity.era era cpu P Q -∗ P -∗
      ▷ (Q -∗ threadWP capacity image fixed whole (.hart gen cpu (k ())) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.barrier kind) k)) post) :=
  wp_update capacity image fixed whole gen era cpu kind k _ P Q post
    (fun g live => power_publish capacity fixed g gen era cpu kind P Q live drains)

theorem wp_identity [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (kind : barrier_kind) (k : Unit → SailM Unit) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      ▷ threadWP capacity image fixed whole (.hart gen cpu (k ())) post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.barrier kind) k)) post) := by
  iintro Hcert Hcontinue
  iapply wp_ghost capacity image fixed whole gen era cpu kind k iprop(True) iprop(True) post $$ Hcert [] [] [Hcontinue]
  · iapply ghostStep_id
  · itrivial
  · iintro !> _
    iexact Hcontinue

theorem wp_ghost_at [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (m : SailM Unit) (kind : barrier_kind) (P Q : IProp GF) (post : Empty → IProp GF)
    (projected : barrierAt m = some kind) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      ghostStep capacity.era era P Q -∗ P -∗
      ▷ (Q -∗ threadWP capacity image fixed whole (.hart gen cpu (barrierResume m)) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu m) post) := by
  obtain ⟨k, rfl, resume⟩ := barrierAt_inv m kind projected
  exact wp_ghost capacity image fixed whole gen era cpu kind k P Q post

theorem wp_publish_at [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (m : SailM Unit) (kind : barrier_kind) (P Q : IProp GF) (post : Empty → IProp GF)
    (projected : barrierAt m = some kind) (drains : fenceDrains kind = true) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      pubStep capacity.era era cpu P Q -∗ P -∗
      ▷ (Q -∗ threadWP capacity image fixed whole (.hart gen cpu (barrierResume m)) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu m) post) := by
  obtain ⟨k, rfl, resume⟩ := barrierAt_inv m kind projected
  exact wp_publish capacity image fixed whole gen era cpu kind k P Q post drains

theorem barrierWPSpec [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : BarrierWPSpec capacity :=
  ⟨wp_ghost capacity, wp_publish capacity⟩

end MachCSL.Logic.BarrierWP
