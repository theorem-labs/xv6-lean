import MachCSL.Machine.AnnotatedPoolDefs

namespace MachCSL.Machine.AnnotatedPool

theorem erase_split (pool : Pool Label) (left right : List Expr) (e : Expr)
    (same : erase pool = left ++ e :: right) :
    ∃ before label after, pool = before ++ (e, label) :: after ∧
      erase before = left ∧ erase after = right := by
  obtain ⟨before, tail, rfl, hbefore, htail⟩ := List.map_eq_append_iff.mp same
  obtain ⟨⟨head, label⟩, after, rfl, rfl, hafter⟩ := List.map_eq_cons_iff.mp htail
  exact ⟨before, label, after, rfl, hbefore, hafter⟩

theorem erase_step [Platform] (image : BootImage) (transition : Transition Label)
    {before after : Config Label} {observations}
    (step : AStep image transition before observations after) :
    PoolStep image (eraseConfig before) observations (eraseConfig after) := by
  letI := language image
  cases step with
  | atomic actual annotation left right =>
    simpa only [eraseConfig, erase, List.map_append, List.map_cons] using
      Iris.ProgramLogic.Language.Step.atomic actual (erase left) (erase right)

theorem erase_steps [Platform] (image : BootImage) (transition : Transition Label)
    {n before after observations} (steps : ASteps image transition n before observations after) :
    PoolSteps image n (eraseConfig before) observations (eraseConfig after) := by
  letI := language image
  induction steps with
  | refl config => exact .refl _
  | cons first next ih => exact .cons (erase_step image transition first) ih

theorem lift_step [Platform] (image : BootImage) (transition : Transition Label)
    (invariant : Config Label → Prop) (covers : Covers image transition invariant)
    (before : Config Label) (after : Configuration) (observations)
    (initial : invariant before) (step : PoolStep image (eraseConfig before) observations after) :
    ∃ annotatedAfter, eraseConfig annotatedAfter = after ∧
      AStep image transition before observations annotatedAfter ∧ invariant annotatedAfter := by
  letI := language image
  obtain ⟨pool, g⟩ := before
  generalize source : eraseConfig (pool, g) = config at step
  cases step with
  | @atomic e state observations e' g' forks actual left right =>
    have hg : g = state := congrArg Prod.snd source
    subst state
    change Step image e g observations e' g' forks at actual
    have hpool : erase pool = left ++ e :: right := congrArg Prod.fst source
    obtain ⟨before, label, after, same, hleft, hright⟩ := erase_split pool left right e hpool
    subst pool
    obtain ⟨label', annotatedForks, hforks, annotation, preserved⟩ :=
      covers before after e label g observations e' g' forks initial actual
    refine ⟨(before ++ (e', label') :: after ++ annotatedForks, g'), ?_, ?_, preserved⟩
    · simp only [eraseConfig, erase, List.map_append, List.map_cons]
      change (erase before ++ e' :: erase after ++ erase annotatedForks, g') = _
      rw [hleft, hright, hforks]
    · apply AStep.atomic (forks := annotatedForks) _ annotation before after
      simpa only [hforks] using actual

theorem lift_steps [Platform] (image : BootImage) (transition : Transition Label)
    (invariant : Config Label → Prop) (covers : Covers image transition invariant)
    (before : Config Label) (after : Configuration) (n : Nat) (observations)
    (initial : invariant before) (steps : PoolSteps image n (eraseConfig before) observations after) :
    ∃ annotatedAfter, eraseConfig annotatedAfter = after ∧
      ASteps image transition n before observations annotatedAfter ∧ invariant annotatedAfter := by
  letI := language image
  generalize source : eraseConfig before = erased at steps
  induction steps generalizing before with
  | refl config =>
    exact ⟨before, source, .refl _, initial⟩
  | @cons n first middle last observations rest firstStep nextSteps ih =>
    rw [← source] at firstStep
    obtain ⟨annotatedMiddle, same, firstAnnotated, preserved⟩ :=
      lift_step image transition invariant covers before middle observations initial firstStep
    obtain ⟨annotatedAfter, finalSame, restAnnotated, finalInvariant⟩ :=
      ih annotatedMiddle preserved same
    exact ⟨annotatedAfter, finalSame, .cons firstAnnotated restAnnotated, finalInvariant⟩

end MachCSL.Machine.AnnotatedPool
