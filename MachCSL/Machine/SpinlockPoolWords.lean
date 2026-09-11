import MachCSL.Machine.SpinlockPoolSpec
import MachCSL.Logic.MemoryExclusiveWPProofs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.SpinlockProtocol

theorem latest_word_bound {g a word time} (latest : LatestWord g a word time) : time ≤ g.log.length :=
  logByte_some_le g.image g.log time (addressAdd a 0) (nthByte word 0) (latest 0 (by decide)).1

theorem latest_word_current {g a word time} (memory : MemoryOK g)
    (latest : LatestWord g a word time) : readBytes g.memory a 4 = some word := by
  apply readBytes_of_bytes
  intro j inside
  rw [memory.1]
  exact latest_flat g.image g.log _ time _ (latest j inside)

theorem latest_word_read {g a word time} (latest : LatestWord g a word time)
    (cpu : CPU) (view : Nat) (above : time ≤ view) :
    ReadsBytes g.image g.log (hartAgent cpu) view a 4 word := by
  intro j inside
  exact read_of_latest g.image g.log (hartAgent cpu) view _ time _ (latest j inside)
    (visible_below _ _ _ _ above)

theorem latest_word_append (g : State) (a : PhysicalAddress) (word : BitVec 32) (author : Agent) :
    LatestWord { g with log := g.log ++ [⟨snapshot a 4 word, author⟩] }
      a word (g.log.length + 1) := by
  have self := MemoryExclusiveWP.snapshot_read (snapshot a 4 word) a 4 word (by decide)
    (fun _ _ same => same)
  intro j inside
  exact latest_append_new g.image g.log ⟨snapshot a 4 word, author⟩ _ _
    (readBytes_spec _ _ _ _ self j inside)

theorem latest_word_frame {g a old time} (latest : LatestWord g a old time)
    (address : PhysicalAddress) (word : BitVec 32) (author : Agent)
    (separate : Disjoint (Footprint a 4) (Footprint address 4)) :
    LatestWord { g with log := g.log ++ [⟨snapshot address 4 word, author⟩] } a old time := by
  intro j inside
  apply latest_append_frame g.image g.log ⟨snapshot address 4 word, author⟩ _ time _ ?_ (latest j inside)
  exact writeBytes_outside empty address _ 4 word
    (fun there => separate _ ⟨j, inside, rfl⟩ there)

theorem phase_holder_owner {g w cpu c B} (phase : PhaseOK g w cpu c)
    (holds : HolderPosition c.phase = some B) : w.owner = some (cpu, B) := by
  cases hp : c.phase <;> simp only [HolderPosition, hp, Option.some.injEq] at holds
  all_goals first | contradiction | skip
  all_goals subst B
  all_goals simp only [PhaseOK, hp] at phase
  all_goals first | exact phase.1.1 | exact phase.1

/-- Unique ownership is a consequence of the concrete pure invariant. The
remaining application obligation is to prove that every actual step preserves it. -/
theorem holder_exclusion {config : Config} {cpu other : CPU} (inv : PoolInv config)
    (left : Holds config cpu) (right : Holds config other) : cpu = other := by
  obtain ⟨on, program, c, B, member, holds⟩ := left
  obtain ⟨_, program', c', C, member', holds'⟩ := right
  obtain ⟨_, _, _, _, _, w, _, locals, _⟩ := inv.2 on
  have owner := phase_holder_owner (locals _ cpu program c member ⟨on, rfl⟩).2 holds
  have owner' := phase_holder_owner (locals _ other program' c' member' ⟨on, rfl⟩).2 holds'
  exact congrArg Prod.fst (Option.some.inj (owner.symm.trans owner'))

theorem initial (g : State) (off : g.power = false) (_zero : g.generation = 0) :
    PoolInv ([(.power, .worker)], g) := by
  refine ⟨⟨?_, rfl, ?_, ?_⟩, ?_⟩
  · intro e label member
    have same := List.mem_singleton.mp member
    cases same
    trivial
  · intro e label member gen generation
    have same := List.mem_singleton.mp member
    cases same
    cases generation
  · intro on; simp [off] at on
  · intro on; simp [off] at on

end MachCSL.Machine.SpinlockPool
