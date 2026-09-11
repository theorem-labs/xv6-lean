import MachCSL.Logic.FsDurXferRunsFractionProofs
import MachCSL.Logic.FsDurBytesProofs

namespace MachCSL.Logic.FsDurXferRuns
open Iris Iris.Std Iris.BI Iris.CMRA
open FsDurBytes (ByteMap leftUnion leftUnion_lookup)

theorem runUnion_nil : runUnion [] = ∅ := rfl
theorem runUnion_cons run runs : runUnion (run :: runs) = leftUnion (runMap run) (runUnion runs) := rfl

theorem runUnion_lookup runs (address : Int) (byte : MachCSL.Memory.Byte) : (runUnion runs)[address]? = some byte →
    ∃ (k : Nat) (run : Run), runs[k]? = some run ∧ (runMap run)[address]? = some byte := by
  induction runs with
  | nil => simp [runUnion]
  | cons head tail ih =>
    rw [runUnion_cons, leftUnion_lookup]
    cases found : (runMap head)[address]? with
    | some value =>
      intro eq
      have same : value = byte := Option.some.inj eq
      subst value
      exact ⟨0, head, rfl, found⟩
    | none =>
      intro eq
      obtain ⟨k, run, get, byteGet⟩ := ih eq
      exact ⟨k + 1, run, get, byteGet⟩

theorem leftUnion_assoc (a b c : ByteMap) : leftUnion (leftUnion a b) c = leftUnion a (leftUnion b c) := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro key
  simp only [leftUnion_lookup]
  cases a[key]? <;> rfl

theorem runUnion_app left right : runUnion (left ++ right) = leftUnion (runUnion left) (runUnion right) := by
  induction left with
  | nil => exact (LawfulPartialMap.union_empty_left (M := Disk.ImageMap)).symm
  | cons run tail ih => simp only [List.cons_append, runUnion_cons, ih, leftUnion_assoc]

theorem runsDisjoint_nil : RunsDisjoint [] := by
  intro k j r1 r2 ne get
  simp at get

theorem runsDisjoint_cons run runs : RunsDisjoint (run :: runs) ↔
    RunsDisjoint runs ∧ ∀ (j : Nat) other, runs[j]? = some other →
      PartialMap.disjoint (M := Disk.ImageMap) (runMap run) (runMap other) := by
  constructor
  · intro disjoint
    exact ⟨fun k j r1 r2 ne getK getJ => disjoint (k + 1) (j + 1) r1 r2 (by omega) getK getJ,
      fun j other get => disjoint 0 (j + 1) run other (by omega) rfl get⟩
  · rintro ⟨tail, head⟩ k j r1 r2 ne getK getJ
    cases k with
    | zero =>
      cases j with
      | zero => exact False.elim (ne rfl)
      | succ j =>
        have eq : run = r1 := Option.some.inj getK
        subst r1
        exact head j r2 getJ
    | succ k =>
      cases j with
      | zero =>
        have eq : run = r2 := Option.some.inj getJ
        subst r2
        exact PartialMap.disjoint_comm (head k r1 getK)
      | succ j => exact tail k j r1 r2 (by omega) getK getJ

theorem runsDisjoint_head run runs (disjoint : RunsDisjoint (run :: runs)) :
    PartialMap.disjoint (M := Disk.ImageMap) (runMap run) (runUnion runs) := by
  intro address overlap
  obtain ⟨byte, found⟩ := Option.isSome_iff_exists.mp overlap.2
  obtain ⟨k, other, get, byteGet⟩ := runUnion_lookup runs address byte found
  exact (runsDisjoint_cons run runs).mp disjoint |>.2 k other get address ⟨overlap.1, by change ((runMap other)[address]?).isSome; simp [byteGet]⟩

theorem runsDisjoint_app left right (disjoint : RunsDisjoint (left ++ right)) :
    RunsDisjoint left ∧ RunsDisjoint right := by
  constructor
  · intro k j r1 r2 ne getK getJ
    apply disjoint k j r1 r2 ne
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp getK).1]; exact getK
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp getJ).1]; exact getJ
  · intro k j r1 r2 ne getK getJ
    apply disjoint (left.length + k) (left.length + j) r1 r2 (by omega)
    · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact getK
    · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact getJ

theorem strip_atShare dq runs : strip (atShare dq runs) = runs := by simp [strip, atShare, List.map_map, Function.comp_def]
theorem strip_cons run runs : strip (run :: runs) = run.2 :: strip runs := rfl

theorem sharesOK_cons run runs : SharesOK (run :: runs) ↔ (¬✓ (run.1 • run.1)) ∧ SharesOK runs := by
  constructor
  · intro ok; exact ⟨ok 0 run rfl, fun k other found => ok (k + 1) other found⟩
  · rintro ⟨head, tail⟩ k other found
    cases k with
    | zero => have eq := Option.some.inj found; subst other; exact head
    | succ k => exact tail k other found

theorem sharesOK_atShare (dq : DFrac) runs (invalid : ¬✓ (dq • dq)) : SharesOK (atShare dq runs) := by
  induction runs with
  | nil => intro k other found; simp [atShare] at found
  | cons run runs ih => exact (sharesOK_cons (dq, run) (atShare dq runs)).mpr ⟨invalid, ih⟩

/-- The total ordered union preserves the first payload even for overlapping runs. -/
theorem ordered_overlap_first_wins (block offset : Int) (first second : MachCSL.Memory.Byte) :
    (runUnion [((block, offset), [first]), ((block, offset), [second])])[block * 1024 + offset]? = some first := by
  rw [runUnion_cons, leftUnion_lookup]
  have found : (runMap ((block, offset), [first]))[block * 1024 + offset]? = some first :=
    (FsDurBytes.byteRun_lookup _ _ _ _).mpr ⟨0, rfl, by simp [runBlock, runOffset]⟩
  rw [found]
  rfl

/-- Positional disjointness permits repeated empty runs, as in the source. -/
theorem repeated_empty_runs block offset : RunsDisjoint [((block, offset), []), ((block, offset), [])] := by
  intro k j r1 r2 ne getK getJ
  have empty : ∀ (k : Nat) run, ([((block, offset), []), ((block, offset), [])] : List Run)[k]? = some run → runMap run = ∅ := by
    intro k run get
    cases k with
    | zero => cases get; rfl
    | succ k => cases k with
      | zero => cases get; rfl
      | succ k => simp at get
  rw [empty k r1 getK]
  exact LawfulPartialMap.disjoint_empty_left _

end MachCSL.Logic.FsDurXferRuns
