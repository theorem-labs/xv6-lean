import MachCSL.Logic.PowerGhostSpec

namespace MachCSL.Logic.PowerGhost
open Iris Iris.BI Iris.CMRA MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance genAuth_timeless γ n : Timeless (genAuth capacity γ n) := by
  letI := capacity.monoNat γ
  unfold genAuth; infer_instance
instance genBorn_timeless γ n : Timeless (genBorn capacity γ n) := by
  letI := capacity.monoNat γ
  unfold genBorn; infer_instance
instance genBorn_persistent γ n : Persistent (genBorn capacity γ n) := by
  letI := capacity.monoNat γ
  unfold genBorn; infer_instance
instance genDead_timeless γ n : Timeless (genDead capacity γ n) := by
  unfold genDead; infer_instance
instance genDead_persistent γ n : Persistent (genDead capacity γ n) := by
  unfold genDead; infer_instance
instance genStarted_timeless γ n : Timeless (genStarted capacity γ n) := by
  unfold genStarted; infer_instance
instance genStarted_persistent γ n : Persistent (genStarted capacity γ n) := by
  unfold genStarted; infer_instance
instance startAuth_timeless γ n : Timeless (startAuth capacity γ n) := by
  unfold startAuth; infer_instance
instance obsAuth_timeless γ h : Timeless (obsAuth capacity γ h) := by
  letI := capacity.observations
  unfold obsAuth; infer_instance
instance obsFrag_timeless γ h : Timeless (obsFrag capacity γ h) := by
  unfold obsFrag; infer_instance
instance obsInterp_timeless γ whole g future : Timeless (obsInterp capacity γ whole g future) := by
  unfold obsInterp; infer_instance

theorem gen_alloc (n : Nat) :
    iprop(⊢ |==> ∃ γ, genAuth capacity γ n ∗ genBorn capacity γ n) := by
  letI := capacity.monoNat 0
  exact MonoNat.own_alloc (.ofNat n)

theorem gen_born γ n : iprop(⊢ genAuth capacity γ n -∗ genBorn capacity γ n) := by
  letI := capacity.monoNat γ
  exact MonoNat.lb_own_get γ (.own 1) (.ofNat n)

theorem gen_born_le γ n lower (le : lower ≤ n) :
    iprop(⊢ genBorn capacity γ n -∗ genBorn capacity γ lower) := by
  letI := capacity.monoNat γ
  exact MonoNat.lb_own_le γ (.ofNat n) (.ofNat lower) le

theorem gen_born_valid γ n generation :
    iprop(⊢ genAuth capacity γ n -∗ genBorn capacity γ generation -∗ ⌜generation ≤ n⌝) := by
  letI := capacity.monoNat γ
  unfold genAuth genBorn
  iintro Ha Hb
  ihave %valid := MonoNat.auth_lb_own_valid γ (.own 1) (.ofNat n) (.ofNat generation) $$ Ha Hb
  ipureintro
  exact valid.2

theorem gen_dead_valid γ n generation :
    iprop(⊢ genAuth capacity γ n -∗ genDead capacity γ generation -∗ ⌜generation < n⌝) := by
  unfold genDead
  iintro Ha Hd
  ihave %valid := gen_born_valid capacity γ n (generation + 1) $$ Ha Hd
  ipureintro
  omega

theorem gen_started_valid γ n generation :
    iprop(⊢ startAuth capacity γ n -∗ genStarted capacity γ generation -∗ ⌜generation < n⌝) :=
  gen_dead_valid capacity γ n generation

theorem gen_update γ n n' (le : n ≤ n') :
    iprop(⊢ genAuth capacity γ n ==∗ genAuth capacity γ n' ∗ genBorn capacity γ n') := by
  letI := capacity.monoNat γ
  exact MonoNat.own_update γ (.ofNat n) (.ofNat n') le

theorem gen_die γ generation :
    iprop(⊢ genAuth capacity γ generation ==∗
      genAuth capacity γ (generation + 1) ∗ genDead capacity γ generation) :=
  gen_update capacity γ generation (generation + 1) (Nat.le_succ _)

theorem start_mark γ generation :
    iprop(⊢ startAuth capacity γ generation ==∗
      startAuth capacity γ (generation + 1) ∗ genStarted capacity γ generation) :=
  gen_die capacity γ generation

/-- Unlike TSO's special zero receipt, this raw unit receipt requires a basic update. -/
theorem gen_born_zero γ : iprop(⊢ |==> genBorn capacity γ 0) := by
  letI := capacity.monoNat γ
  exact MonoNat.lb_own_0 γ

theorem obs_alloc (history : List Observation) :
    iprop(⊢ |==> ∃ γ, obsAuth capacity γ history ∗ obsFrag capacity γ history) := by
  letI := capacity.observations
  unfold obsFrag obsAuth
  imod ghost_var_alloc history with ⟨%γ, H⟩
  imodintro
  iexists γ
  have split := ghost_var_split (GF := GF) γ history (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at split
  iapply split $$ H

theorem obs_agree γ h1 h2 :
    iprop(⊢ obsAuth capacity γ h1 -∗ obsFrag capacity γ h2 -∗ ⌜h1 = h2⌝) := by
  letI := capacity.observations
  unfold obsFrag obsAuth
  exact ghost_var_agree γ h1 (.own (1 : Qp).half) h2 (.own (1 : Qp).half)

theorem obs_update γ history history' :
    iprop(⊢ obsAuth capacity γ history -∗ obsFrag capacity γ history ==∗
      obsAuth capacity γ history' ∗ obsFrag capacity γ history') := by
  letI := capacity.observations
  exact ghost_var_update_halves history' γ history history

theorem obs_interp_silent [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (forks) (step : Step image e g [] e' g' forks) γ whole future :
    iprop(obsInterp capacity γ whole g future ⊢ obsInterp capacity γ whole g' future) := by
  unfold obsInterp
  iintro ⟨%history, %total, %wf, Ha⟩
  iexists history
  iframe Ha
  ipureintro
  exact ⟨total, by simpa using step_observations_ok image e e' g g' [] forks history wf step⟩

theorem obs_interp_close [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (events forks history future whole) (step : Step image e g events e' g' forks)
    (wf : ObservationsOK history g) (total : history ++ (events ++ future) = whole) γ :
    iprop(obsAuth capacity γ (history ++ events) ⊢ obsInterp capacity γ whole g' future) := by
  unfold obsInterp
  iintro Ha
  iexists history ++ events
  iframe Ha
  ipureintro
  exact ⟨by simpa only [List.append_assoc] using total,
    step_observations_ok image e e' g g' events forks history wf step⟩

theorem obs_interp_finished γ whole g :
    iprop(obsInterp capacity γ whole g [] ⊢ obsAuth capacity γ whole ∗ ⌜ObservationsOK whole g⌝) := by
  unfold obsInterp
  iintro ⟨%history, %total, %wf, Ha⟩
  simp only [List.append_nil] at total
  subst history
  iframe Ha
  ipureintro
  exact wf

theorem startCount_step [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (events forks) (step : Step image e g events e' g' forks) : startCount g ≤ startCount g' := by
  cases step with
  | hartLive generation cpu m m' g g' live h =>
    simp only [startCount, hart_generation _ _ _ _ _ h, hart_power _ _ _ _ _ h]
    exact Nat.le_refl _
  | hartDead => exact Nat.le_refl _
  | uartLive => exact Nat.le_refl _
  | uartDead => exact Nat.le_refl _
  | diskLive => exact Nat.le_refl _
  | diskDead => exact Nat.le_refl _
  | plicLive => exact Nat.le_refl _
  | plicDead => exact Nat.le_refl _
  | power g events next forks h =>
    cases h with
    | off on => simp [startCount, powerOff, on]
    | on off next shape => simp [startCount, off, shape.1, shape.2.2.1]

theorem counter_step [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (events forks) (step : Step image e g events e' g' forks) (names : Names) :
    iprop(counterInterp capacity names g ⊢ |==> counterInterp capacity names g') := by
  unfold counterInterp startAuth
  iintro ⟨Hg, Hs⟩
  imod gen_update capacity names.generation g.generation g'.generation
    (step_generation_monotone image e e' g g' events forks step) $$ Hg with ⟨Hg, _⟩
  imod gen_update capacity names.started (startCount g) (startCount g')
    (startCount_step image e e' g g' events forks step) $$ Hs with ⟨Hs, _⟩
  imodintro
  iframe Hg Hs

/-- Allocate only these fixed components, with a caller-supplied real trace invariant. -/
theorem fixed_alloc (g : State) (history future : List Observation) (wf : ObservationsOK history g) :
    iprop(⊢ |==> ∃ names : Names, counterInterp capacity names g ∗
      obsInterp capacity names.observations (history ++ future) g future ∗
      obsFrag capacity names.observations history) := by
  imod gen_alloc capacity g.generation with ⟨%γg, Hg, _⟩
  imod gen_alloc capacity (startCount g) with ⟨%γs, Hs, _⟩
  imod obs_alloc capacity history with ⟨%γo, Ho, Hf⟩
  imodintro
  iexists (Names.mk γg γs γo)
  unfold counterInterp startAuth obsInterp
  iframe Hg Hs Hf
  iexists history
  iframe Ho
  ipureintro
  exact ⟨rfl, wf⟩

/-- The ordinary start-counter authority can move to any larger count. -/
theorem start_update γ n n' (le : n ≤ n') :
    iprop(⊢ startAuth capacity γ n ==∗ startAuth capacity γ n') := by
  unfold startAuth
  iintro H
  imod gen_update capacity γ n n' le $$ H with ⟨H, _⟩
  imodintro
  iexact H

instance obsLedger_timeless γ R [∀ h, Timeless (R h)] :
    Timeless (obsLedger capacity γ R) := by
  unfold obsLedger
  infer_instance

theorem powerGhostSpec : PowerGhostSpec capacity where
  genAlloc := gen_alloc capacity
  genUpdate := gen_update capacity
  genDie := gen_die capacity
  startMark := start_mark capacity
  genValid := gen_born_valid capacity
  deadValid := gen_dead_valid capacity
  startedValid := gen_started_valid capacity
  obsAlloc := obs_alloc capacity
  obsAgree := obs_agree capacity
  obsUpdate := obs_update capacity
  obsSilent := obs_interp_silent capacity
  obsClose := obs_interp_close capacity
  obsFinished := obs_interp_finished capacity
  counterStep := counter_step capacity
  fixedAlloc := fixed_alloc capacity

end MachCSL.Logic.PowerGhost
