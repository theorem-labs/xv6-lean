import MachCSL.Machine.SpinlockPoolDefs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic

def initialWords : Words := ⟨none, 0, 0#32, 0⟩

theorem boot_word {g : State} (facts : BootFacts SpinlockImage.image g)
    (address : PhysicalAddress) (word : BitVec 32)
    (read : readBytes (loadedRam SpinlockImage.image) address 4 = some word) :
    LatestWord g address word 0 := by
  obtain ⟨_, memory, _, _, _, _, _, log, initial, _⟩ := facts
  intro j inside
  constructor
  · change g.image (addressAdd address j) = some (nthByte word j)
    rw [initial, memory]
    exact readBytes_spec _ _ _ _ read j inside
  · intro time positive
    cases time with
    | zero => omega
    | succ n => simp [logByte, log]

theorem boot_words {g : State} (facts : BootFacts SpinlockImage.image g) :
    WordsOK g initialWords :=
  ⟨boot_word facts _ _ SpinlockImage.lock_initial,
    boot_word facts _ _ SpinlockImage.counter_initial⟩

theorem boot_cursor {g : State} (facts : BootFacts SpinlockImage.image g) (cpu : CPU) :
    CursorControl g cpu (.pure ()) (initialCursor g cpu) ∧
      PhaseOK g initialWords cpu (initialCursor g cpu) := by
  refine ⟨⟨fun _ _ => rfl, rfl, .pure ?_⟩, True.intro⟩
  exact ⟨⟨0, by decide⟩, SpinlockFamily.boot g facts cpu⟩

theorem fresh_hart_iff (g : State) (gen : Nat) (cpu : CPU) (program : SailM Unit) (c : Cursor) :
    (Expr.hart gen cpu program, Label.hart c) ∈ freshForks g ↔
      gen = g.generation ∧ program = .pure () ∧ c = initialCursor g cpu := by
  unfold freshForks
  rw [List.mem_append]
  constructor
  · rintro (member | member)
    · obtain ⟨other, same⟩ := List.mem_ofFn.mp member
      have same' : g.generation = gen ∧ other = cpu ∧ (.pure () : SailM Unit) = program ∧
          initialCursor g other = c := by
        simpa only [loop, Prod.mk.injEq, Expr.hart.injEq, Label.hart.injEq, and_assoc] using same
      obtain ⟨rfl, rfl, rfl, rfl⟩ := same'
      exact ⟨rfl, rfl, rfl⟩
    · simp at member
  · rintro ⟨rfl, rfl, rfl⟩
    exact Or.inl (List.mem_ofFn.mpr ⟨cpu, rfl⟩)

theorem fresh_cursors {g : State} (facts : BootFacts SpinlockImage.image g) :
    LiveCursors (freshForks g) g initialWords := by
  intro gen cpu program c member live
  obtain ⟨rfl, rfl, rfl⟩ := (fresh_hart_iff g gen cpu program c).mp member
  exact boot_cursor facts cpu

theorem fresh_owner (pool : Pool) (g : State) : OwnerPresent pool g initialWords := by
  intro cpu position impossible
  cases impossible

theorem fresh_current (g : State) : currentHarts (freshForks g) g.generation = List.finRange 8 := by
  simp [freshForks, currentHarts, loop]
  rfl

end MachCSL.Machine.SpinlockPool
