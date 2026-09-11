import MachCSL.Machine.SpinlockPoolBootProofs
import MachCSL.Machine.SpinlockPoolWorkerCoverProofs

namespace MachCSL.Machine.SpinlockPool

theorem fresh_labels (g : State) (e : Expr) (label : Label)
    (member : (e, label) ∈ freshForks g) : LabelMatches e label := by
  rcases List.mem_append.mp member with hart | worker
  · obtain ⟨cpu, same⟩ := List.mem_ofFn.mp hart
    cases same
    trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at worker
    rcases worker with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial

theorem fresh_generation (g : State) (e : Expr) (label : Label)
    (member : (e, label) ∈ freshForks g) (gen : Nat)
    (found : generationOf e = some gen) : gen = g.generation := by
  rcases List.mem_append.mp member with hart | worker
  · obtain ⟨cpu, same⟩ := List.mem_ofFn.mp hart
    cases same
    exact (Option.some.inj found).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at worker
    rcases worker with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact (Option.some.inj found).symm

theorem off_current_empty {pool : Pool} {g : State} (shape : Shape pool g) (off : g.power = false) :
    currentHarts pool g.generation = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro entry member
  obtain ⟨e, label⟩ := entry
  cases e with
  | hart gen cpu program =>
    have strict := (shape.generations _ label member gen rfl).2 off
    exact if_neg (by omega)
  | uart | disk | plic | power => rfl

theorem power_on_shape {pool : Pool} {g g' : State} (shape : Shape pool g)
    (off : g.power = false) (boot : BootShape SpinlockImage.image g g') :
    Shape (pool ++ freshForks g') g' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e label member
    rcases List.mem_append.mp member with old | fresh
    · exact shape.labels e label old
    · exact fresh_labels g' e label fresh
  · rw [List.filter_append, List.length_append, shape.power]
    rfl
  · intro e label member gen found
    refine ⟨?_, ?_⟩
    · rcases List.mem_append.mp member with old | fresh
      · rw [boot.1]
        exact (shape.generations e label old gen found).1
      · rw [fresh_generation g' e label fresh gen found]
        exact Nat.le_refl _
    · intro impossible
      have on := boot.2.2.1
      rw [on] at impossible
      contradiction
  · intro on
    change (currentHarts (pool ++ freshForks g') g'.generation).Perm _
    have split : currentHarts (pool ++ freshForks g') g'.generation =
        currentHarts pool g'.generation ++ currentHarts (freshForks g') g'.generation := List.filterMap_append
    rw [split, fresh_current, boot.1, off_current_empty shape off, List.nil_append]

theorem power_on_frame {pool : Pool} {g g' : State} (inv : PoolInv (pool, g))
    (off : g.power = false) (boot : BootShape SpinlockImage.image g g') :
    PoolInv (pool ++ freshForks g', g') := by
  refine ⟨power_on_shape inv.1 off boot, ?_⟩
  intro on
  have facts := boot.2.2
  obtain ⟨_, memory, _, _, _, reset, reservations, log, image, views⟩ := boot.2.2
  refine ⟨boot_memory_ok _ g' facts, boot_reservations_ok _ g' facts,
    image.trans memory, reset, ?_, initialWords, boot_words facts, ?_, fresh_owner _ _⟩
  · rw [log]
    exact SpinlockCodeIntegrity.nil
  · intro gen cpu program c member live
    rcases List.mem_append.mp member with old | fresh
    · have strict := (inv.1.generations _ (.hart c) old gen rfl).2 off
      change gen < g.generation at strict
      have same := boot.1.symm.trans live.2
      omega
    · exact fresh_cursors facts gen cpu program c fresh live

theorem erase_fresh (g : State) : AnnotatedPool.erase (freshForks g) = powerFork g.generation := rfl

theorem cover_power_on [Platform] {left right : Pool} {g g' : State}
    {e' : Expr} {forks : List Expr}
    (inv : PoolInv (left ++ (.power, .worker) :: right, g))
    (step : Step SpinlockImage.image .power g [.powerOn] e' g' forks) :
    Covered left right .power .worker g [.powerOn] e' g' forks := by
  cases step with
  | power g observations next forks action =>
    cases action with
    | on off g' boot =>
      refine ⟨.worker, freshForks g', ?_, .powerOn off, ?_⟩
      · rw [erase_fresh, boot.1]
      · exact power_on_frame inv off boot

end MachCSL.Machine.SpinlockPool
