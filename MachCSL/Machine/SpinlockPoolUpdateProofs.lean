import MachCSL.Machine.SpinlockPoolSwap

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

theorem select_eq_some {α : Type} {predicate : α → Prop} {value : α}
    (valid : predicate value)
    (unique : ∀ other, predicate other → other = value) : select predicate = some value := by
  classical
  unfold select
  split
  next found => rw [unique found.choose found.choose_spec]
  next absent => exact False.elim (absent ⟨value, valid⟩)

theorem latest_unique {g : State} {address : PhysicalAddress} {v w : Byte} {t u : Nat}
    (left : Latest g.image g.log address t v) (right : Latest g.image g.log address u w) :
    t = u ∧ v = w := by
  have time : t = u := by
    rcases (show t < u ∨ t = u ∨ u < t by omega) with less | equal | greater
    · have absent := left.2 u less
      rw [right.1] at absent
      contradiction
    · exact equal
    · have absent := right.2 t greater
      rw [left.1] at absent
      contradiction
  subst u
  exact ⟨rfl, Option.some.inj (left.1.symm.trans right.1)⟩

theorem latest_word_unique {g : State} {address : PhysicalAddress} {v w : BitVec 32} {t u : Nat}
    (left : LatestWord g address v t) (right : LatestWord g address w u) :
    v = w ∧ t = u := by
  refine ⟨Memory.bv_eq_of_bytes v w (fun j bound => (latest_unique (left j bound) (right j bound)).2),
    (latest_unique (left 0 (by decide)) (right 0 (by decide))).1⟩

theorem latest_pair_of_word {g : State} {address : PhysicalAddress} {v : BitVec 32} {t : Nat}
    (latest : LatestWord g address v t) : latestPair g address = some (v, t) := by
  apply select_eq_some (predicate := fun pair : BitVec 32 × Nat => LatestWord g address pair.1 pair.2) latest
  intro pair other
  exact Prod.ext (latest_word_unique other latest).1 (latest_word_unique other latest).2

theorem instruction_address_injective : Function.Injective SpinlockImage.instructionAddress := by
  intro i j equal
  have same := congrArg BitVec.toNat equal
  rw [SpinlockImage.instruction_address, SpinlockImage.instruction_address] at same
  apply Fin.ext
  omega

theorem boundary_index_of_pc {rs : RegisterFile} {i : Fin 17}
    (pc : rs .PC = SpinlockImage.instructionAddress i) : boundaryIndex rs = some i := by
  apply select_eq_some (predicate := fun j => rs .PC = SpinlockImage.instructionAddress j) pc
  intro j other
  exact instruction_address_injective (other.symm.trans pc)

theorem committed_acquire {g : State} {v : BitVec 32} {t : Nat}
    (latest : LatestWord g SpinlockImage.counterAddress v t) :
    committedPhase g (.reserved 0#32) = some (.held (g.log.length + 1) v t) := by
  simp [committedPhase, latest_pair_of_word latest]

theorem update_restart [Platform] (g : State) (cpu : CPU) (c : Cursor) (i : Fin 17)
    (pc : c.registers .PC = SpinlockImage.instructionAddress i) :
    nextCursor g (RestartWP.clearReservation g cpu) cpu (.pure ()) c =
      some { c with fetch := i, reservation := none } := by
  simp [nextCursor, boundary_index_of_pc pc]

theorem update_read_register (g g' : State) (cpu : CPU) (c : Cursor) (r : Register)
    (k : RegisterType r → SailM Unit) :
    nextCursor g g' cpu (.impure (.readReg r) k) c = some c := rfl

theorem update_write_register (g : State) (cpu : CPU) (c : Cursor) (r : Register)
    (value : RegisterType r) (k : Unit → SailM Unit) (owned : EventWP.IsOwned r) :
    nextCursor g (EraState.writeRegister g cpu r value) cpu (.impure (.writeReg r value) k) c =
      some { c with registers := Sail.Registers.write c.registers r value } := by
  simp [nextCursor, owned]

theorem update_exclusive_blocked (g : State) (cpu : CPU) (c : Cursor)
    (k : MemoryReadWP.ReadResult 4 → SailM Unit) (idle : c.phase = .idle) :
    nextCursor g (RestartWP.clearReservation g cpu) cpu (.impure (.readMem 4 lockRead) k) c =
      some { c with reservation := none } := by
  have kind : accessExclusive lockRead.access_kind = true := rfl
  simp [nextCursor, idle, kind, RestartWP.clearReservation, updateHart]

theorem update_exclusive_success (g : State) (cpu : CPU) (c : Cursor)
    (k : MemoryReadWP.ReadResult 4 → SailM Unit) (idle : c.phase = .idle)
    (word : BitVec 32) (binary : word = 0#32 ∨ word = 1#32)
    (read : readBytes g.memory SpinlockImage.lockAddress 4 = some word) :
    nextCursor g (MemoryExclusiveWP.acquired g cpu SpinlockImage.lockAddress 4 word)
      cpu (.impure (.readMem 4 lockRead) k) c =
      some { c with phase := .reserved word, reservation := some (snapshot SpinlockImage.lockAddress 4 word) } := by
  have kind : accessExclusive lockRead.access_kind = true := rfl
  simp [nextCursor, idle, kind, MemoryExclusiveWP.acquired_reservation, read, binary]

theorem update_swap_effect {g : State} {cpu : CPU} {c : Cursor} {w : Words} {old : BitVec 32}
    {g' : State} {c' : Cursor} {w' : Words}
    (k : MemoryWriteWP.WriteResult → SailM Unit) (phase : c.phase = .reserved old)
    (words : WordsOK g w) (effect : SwapEffect g cpu c w old g' c' w') :
    nextCursor g g' cpu (.impure (.writeMem 4 swapWrite) k) c = some c' := by
  cases effect with
  | blocked => simp [nextCursor, expectedWrite, phase]
  | won zero free =>
    subst old
    simp [nextCursor, expectedWrite, phase, MemoryWriteWP.writeState,
      committed_acquire words.2]
  | lost one =>
    subst old
    simp [nextCursor, expectedWrite, phase, MemoryWriteWP.writeState, committedPhase]

theorem next_cursor_functional {g g' : State} {cpu : CPU} {program : SailM Unit} {c a b : Cursor}
    (first : nextCursor g g' cpu program c = some a)
    (second : nextCursor g g' cpu program c = some b) : a = b :=
  Option.some.inj (first.symm.trans second)

/-- Uniqueness of the labels for the same selected occurrence and same actual
pre/post step. This does not infer an occurrence index from an erased trace. -/
theorem transition_functional [Platform] {before : Expr × Label} {g g' : State}
    {observations : List Observation} {after : Expr} {a b : Label} {forksA forksB : Pool}
    (first : Transition before g observations (after, a) g' forksA)
    (second : Transition before g observations (after, b) g' forksB) :
    a = b ∧ forksA = forksB := by
  cases first <;> cases second
  all_goals first
    | exact ⟨rfl, rfl⟩
    | contradiction
    | exact ⟨congrArg Label.hart (next_cursor_functional (by assumption) (by assumption)), rfl⟩

end MachCSL.Machine.SpinlockPool
