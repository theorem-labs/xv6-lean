import MachCSL.Machine.SpinlockPoolStoreTransports

namespace MachCSL.Machine.SpinlockPool

theorem current_append (left right : Pool) (gen : Nat) :
    currentHarts (left ++ right) gen = currentHarts left gen ++ currentHarts right gen :=
  List.filterMap_append

theorem current_hart_member {pool : Pool} {gen : Nat} {cpu : CPU} {program : SailM Unit} {c : Cursor}
    (member : (Expr.hart gen cpu program, Label.hart c) ∈ pool) : cpu ∈ currentHarts pool gen := by
  apply List.mem_filterMap.mpr
  exact ⟨_, member, if_pos rfl⟩

/-- Occurrence uniqueness, rather than equality of erased expression values. -/
theorem context_different_cpu {left right : Pool} {g : State} {gen : Nat} {cpu other : CPU}
    {program otherProgram : SailM Unit} {c otherCursor : Cursor}
    (shape : Shape (left ++ (.hart gen cpu program, .hart c) :: right) g)
    (live : ThreadLive g gen)
    (member : (Expr.hart gen other otherProgram, Label.hart otherCursor) ∈ left ++ right) : other ≠ cpu := by
  intro same
  subst other
  have nodup := (shape.current live.1).nodup_iff.mpr (List.nodup_finRange 8)
  rw [live.2] at nodup
  change (currentHarts (left ++ (.hart gen cpu program, .hart c) :: right) gen).Nodup at nodup
  rw [current_append] at nodup
  have selected : currentHarts ((Expr.hart gen cpu program, Label.hart c) :: right) gen =
      cpu :: currentHarts right gen := by simp [currentHarts]
  rw [selected] at nodup
  have context := current_hart_member member
  rw [current_append, List.mem_append] at context
  obtain ⟨leftNodup, rightNodup, disjoint⟩ := List.nodup_append.mp nodup
  rcases context with inLeft | inRight
  · exact disjoint cpu inLeft cpu (by simp) rfl
  · exact (List.nodup_cons.mp rightNodup).1 inRight

theorem selected_owner_phase {left right : Pool} {g : State} {gen : Nat} {cpu : CPU}
    {program : SailM Unit} {c : Cursor} {w : Words} {B : Nat}
    (shape : Shape (left ++ (.hart gen cpu program, .hart c) :: right) g)
    (live : ThreadLive g gen)
    (owners : OwnerPresent (left ++ (.hart gen cpu program, .hart c) :: right) g w)
    (owner : w.owner = some (cpu, B)) : HolderPosition c.phase = some B := by
  obtain ⟨otherProgram, otherCursor, member, held⟩ := owners cpu B owner
  rw [live.2] at member
  rcases List.mem_append.mp member with inLeft | selectedOrRight
  · exact False.elim (context_different_cpu shape live (List.mem_append_left right inLeft) rfl)
  · rcases List.mem_cons.mp selectedOrRight with same | inRight
    · have equal : otherCursor = c := Label.hart.inj (congrArg Prod.snd same)
      exact equal ▸ held
    · exact False.elim (context_different_cpu shape live (List.mem_append_right left inRight) rfl)

theorem shape_replace_hart {left right : Pool} {g g' : State} {gen : Nat} {cpu : CPU}
    {program program' : SailM Unit} {c c' : Cursor}
    (shape : Shape (left ++ (.hart gen cpu program, .hart c) :: right) g)
    (generation : g'.generation = g.generation) (power : g'.power = g.power) :
    Shape (left ++ (.hart gen cpu program', .hart c') :: right) g' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e label member
    rcases List.mem_append.mp member with inLeft | selectedOrRight
    · exact shape.labels e label (List.mem_append_left _ inLeft)
    · rcases List.mem_cons.mp selectedOrRight with same | inRight
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        trivial
      · exact shape.labels e label (List.mem_append_right _ (List.mem_cons_of_mem _ inRight))
  · simpa only [List.filter_append, List.filter_cons, Bool.false_eq_true, ↓reduceIte] using shape.power
  · intro e label member tagged found
    rw [generation, power]
    rcases List.mem_append.mp member with inLeft | selectedOrRight
    · exact shape.generations e label (List.mem_append_left _ inLeft) tagged found
    · rcases List.mem_cons.mp selectedOrRight with selected | inRight
      · cases selected
        exact shape.generations (.hart gen cpu program) (.hart c)
          (List.mem_append_right _ (List.mem_cons_self ..)) tagged found
      · exact shape.generations e label
          (List.mem_append_right _ (List.mem_cons_of_mem _ inRight)) tagged found
  · intro on
    rw [power] at on
    rw [generation]
    simpa only [currentHarts, List.filterMap_append, List.filterMap_cons] using shape.current on

end MachCSL.Machine.SpinlockPool
