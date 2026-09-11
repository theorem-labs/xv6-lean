import MachCSL.Logic.RestartWPSpec
import MachCSL.Logic.RegisterWPProofs
import MachCSL.Logic.ReservationProofs

namespace MachCSL.Logic.RestartWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Machine

theorem clearReservation_ok (g : State) (cpu : CPU) (ok : ReservationsOK g) :
    ReservationsOK (clearReservation g cpu) := by
  intro other r present
  change updateHart g.reservations cpu none other = some r at present
  by_cases same : other = cpu
  · simp [updateHart, same] at present
  · simp only [updateHart, if_neg same] at present
    exact ok other r present

theorem writeBack_clear (g : State) (cpu : CPU) :
    writeBack g cpu {focus g cpu with reservation := none} = clearReservation g cpu := by
  have same {α : Type} (f : CPU → α) : updateHart f cpu (f cpu) = f := by
    funext other
    by_cases h : other = cpu <;> simp [updateHart, h]
  simp only [writeBack, focus, clearReservation, same]

theorem restart_machine_step [Platform] (image : BootImage) (g : State) (generation : Nat)
    (cpu : CPU) (tick : Bool) (live : ThreadLive g generation) :
    Step image (.hart generation cpu (.pure ())) g [] (.hart generation cpu (cycle tick))
      (clearReservation g cpu) [] := by
  apply Step.hartLive _ _ _ _ _ _ live
  exact ⟨_, restart_step Devices.bus _ _ g.image (focus g cpu) tick, (writeBack_clear g cpu).symm⟩

theorem restart_successors [Platform] (image : BootImage) (g : State) (generation : Nat)
    (cpu : CPU) (live : ThreadLive g generation) (events : List Observation)
    (e' : Expr) (g' : State) (forks : List Expr)
    (step : Step image (.hart generation cpu (.pure ())) g events e' g' forks) :
    ∃ tick, e' = .hart generation cpu (cycle tick) ∧ g' = clearReservation g cpu ∧
      forks = [] ∧ events = [] := by
  cases step with
  | hartDead _ _ _ _ dead => exact False.elim (dead live)
  | hartLive _ _ _ next _ _ _ h =>
    obtain ⟨after, ⟨tick, rfl, rfl⟩, rfl⟩ := h
    exact ⟨tick, rfl, writeBack_clear g cpu, rfl, rfl⟩

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

theorem era_clear (era : Era.Record) (g : State) (cpu : CPU) :
    iprop(⊢ Era.interp capacity.era era g -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu ==∗
      Era.interp capacity.era era (clearReservation g cpu) ∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu none) := by
  unfold Era.interp
  iintro ⟨Hregs, Hheap, Hdev, Hdisk, Htso, Hresv, %ok⟩ Hany
  imod Reservations.resvAny_update capacity.era.reservations era.reservations g.reservations cpu none
    $$ Hresv Hany with ⟨Hresv, Hnone⟩
  imodintro
  have heap : Era.heapInterpAt capacity.era era (clearReservation g cpu) = Era.heapInterpAt capacity.era era g := rfl
  have tso : Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (clearReservation g cpu) =
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g := rfl
  rw [heap, tso]
  unfold clearReservation
  iframe
  ipureintro
  exact clearReservation_ok g cpu ok

theorem power_clear (fixed : MachineInterp.FixedNames) (g : State) (generation : Nat)
    (era : Era.Record) (cpu : CPU) (live : ThreadLive g generation) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed generation era -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu ==∗
      MachineInterp.powerInterp capacity fixed (clearReservation g cpu) ∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu none) :=
  MachineInterp.live_update capacity fixed g (clearReservation g cpu) generation era live rfl rfl rfl _ _
    (era_clear capacity era g cpu)

/-- Restart is a real machine transition: it clears the reservation and permits
both clock choices. The continuation is guarded by that transition. -/
theorem wp_restart [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      ▷ (∀ tick : Bool, Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        DeadThread.threadWP capacity image fixed whole (.hart generation cpu (cycle tick)) post) -∗
      DeadThread.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold DeadThread.threadWP
  iintro #Hcert Hresv Hcontinue
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS]
  iunfold MachineInterp.stateInterp at Hstate
  icases Hstate with ⟨Hp, Ho⟩
  ihave %cases := MachineInterp.generation_cases capacity fixed g generation era $$ Hp Hcert
  rcases cases with older | live
  · ihave #Hdead := RegisterWP.power_dead capacity fixed g generation older $$ Hp
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
      · have tail := DeadThread.wp_dead capacity image fixed whole (.hart generation cpu (.pure ())) generation post rfl
        unfold DeadThread.threadWP at tail
        iapply tail $$ Hdead
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
  · iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, clearReservation g cpu, [], restart_machine_step image g generation cpu false live⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨tick, rfl, rfl, rfl, rfl⟩ := restart_successors image g generation cpu live events e' g' forks step
      imod power_clear capacity fixed g generation era cpu live $$ Hp Hcert Hresv with ⟨Hp, Hresv⟩
      isimp only [List.nil_append] at Ho
      ihave Ho := PowerGhost.obs_interp_silent capacity.power image _ _ g _ []
        (restart_machine_step image g generation cpu tick live) fixed.observations whole future $$ Ho
      imod Hback
      imodintro
      simp only [List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · iapply Hcontinue $$ %tick Hresv
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial

/-- Exact fragment-shaped source interface (`RiscvExec.wp_hart_restart`). -/
theorem wp_restart_fragment [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (old : Reservations.Value)
    (post : Empty → IProp GF) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu old -∗
      ▷ (∀ tick : Bool, Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        DeadThread.threadWP capacity image fixed whole (.hart generation cpu (cycle tick)) post) -∗
      DeadThread.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) := by
  iintro Hcert Hresv Hcontinue
  ihave Hresv := Reservations.resvAny_intro capacity.era.reservations era.reservations cpu old $$ Hresv
  iapply wp_restart capacity image fixed whole generation era cpu post $$ Hcert Hresv Hcontinue

theorem restartWPSpec [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : RestartWPSpec capacity :=
  ⟨wp_restart capacity⟩

end MachCSL.Logic.RestartWP
