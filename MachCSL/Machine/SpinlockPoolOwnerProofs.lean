import MachCSL.Machine.SpinlockPoolSceneryProofs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

def writeEvent (program : SailM Unit) : Bool :=
  match program with
  | .impure (.writeMem _ _) _ => true
  | _ => false

theorem plain_holder {s s' : Phase} {n : Nat} {req : ReadRequest n} {word : BitVec (8 * n)}
    (step : PlainStep s n req word s') : HolderPosition s' = HolderPosition s := by cases step; rfl

theorem exclusive_holder {s s' : Phase} {n : Nat} {req : ReadRequest n} {word : BitVec (8 * n)}
    (step : ExclusiveStep s n req word s') : HolderPosition s' = HolderPosition s := by cases step; rfl

theorem barrier_holder {s s' : Phase} {kind : barrier_kind}
    (step : BarrierStep s kind s') : HolderPosition s' = HolderPosition s := by cases step; rfl

theorem edge_nonwrite_holder [Platform] {cpu : CPU} {c c' : Cursor} {program program' : SailM Unit}
    (edge : CursorEdge cpu c program c' program') (nonwrite : writeEvent program = false) :
    HolderPosition c'.phase = HolderPosition c.phase := by
  cases edge
  all_goals first
    | exact rfl
    | exact plain_holder (by assumption)
    | exact exclusive_holder (by assumption)
    | exact barrier_holder (by assumption)
    | contradiction

def OwnerFacts (w w' : Words) (cpu : CPU) (c' : Cursor) : Prop :=
  OtherOwners w w' cpu ∧ OtherOwnersBack w w' cpu ∧
    ∀ B, w'.owner = some (cpu, B) → HolderPosition c'.phase = some B

theorem owner_same {w : Words} {cpu : CPU} {c c' : Cursor}
    (self : ∀ B, w.owner = some (cpu, B) → HolderPosition c.phase = some B)
    (same : HolderPosition c'.phase = HolderPosition c.phase) : OwnerFacts w w cpu c' := by
  refine ⟨fun _ _ _ owner => ⟨owner, rfl, rfl⟩, fun _ _ _ owner => owner, ?_⟩
  intro B owner
  exact same.trans (self B owner)

theorem other_owner_impossible {w : Words} {cpu other : CPU} {B C : Nat}
    (owner : w.owner = some (cpu, B)) (different : other ≠ cpu)
    (otherOwner : w.owner = some (other, C)) : False := by
  exact different (congrArg Prod.fst (Option.some.inj (otherOwner.symm.trans owner)))

theorem swap_owner_facts {g g' : State} {cpu : CPU} {c c' : Cursor} {w w' : Words} {old : BitVec 32}
    (phase : c.phase = .reserved old)
    (self : ∀ B, w.owner = some (cpu, B) → HolderPosition c.phase = some B)
    (effect : SwapEffect g cpu c w old g' c' w') : OwnerFacts w w' cpu c' := by
  cases effect with
  | blocked => exact owner_same self rfl
  | won zero free =>
    refine ⟨?_, ?_, ?_⟩
    · intro other B different owner
      rw [free] at owner
      contradiction
    · intro other B different owner
      have same : cpu = other := congrArg Prod.fst (Option.some.inj owner)
      exact False.elim (different same.symm)
    · intro B owner
      have same : g.log.length + 1 = B := congrArg Prod.snd (Option.some.inj owner)
      exact congrArg some same
  | lost one =>
    refine ⟨fun _ _ _ owner => ⟨owner, rfl, rfl⟩, fun _ _ _ owner => owner, ?_⟩
    intro B owner
    have impossible := self B owner
    rw [phase] at impossible
    contradiction

theorem counter_owner_facts {g g' : State} {cpu : CPU} {c c' : Cursor} {w w' : Words}
    {B : Nat} {v : BitVec 32} {t : Nat}
    (self : ∀ C, w.owner = some (cpu, C) → HolderPosition c.phase = some C)
    (effect : CounterEffect g cpu c w B v t g' c' w') : OwnerFacts w w' cpu c' := by
  cases effect with
  | blocked => exact owner_same self rfl
  | committed owner =>
    refine ⟨?_, fun _ _ _ oldOwner => oldOwner, ?_⟩
    · intro other C different otherOwner
      exact False.elim (other_owner_impossible owner different otherOwner)
    · intro C selected
      have same : B = C := congrArg Prod.snd (Option.some.inj (owner.symm.trans selected))
      exact congrArg some same

theorem unlock_owner_facts {g g' : State} {cpu : CPU} {c c' : Cursor} {w w' : Words} {B : Nat}
    (self : ∀ C, w.owner = some (cpu, C) → HolderPosition c.phase = some C)
    (effect : UnlockEffect g cpu c w B g' c' w') : OwnerFacts w w' cpu c' := by
  cases effect with
  | blocked => exact owner_same self rfl
  | committed owner =>
    refine ⟨?_, ?_, ?_⟩
    · intro other C different otherOwner
      exact False.elim (other_owner_impossible owner different otherOwner)
    · intro other C different impossible
      cases impossible
    · intro C impossible
      cases impossible

end MachCSL.Machine.SpinlockPool
