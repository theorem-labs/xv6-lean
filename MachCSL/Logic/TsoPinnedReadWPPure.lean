import MachCSL.Logic.TsoPinnedReadWPDefs
import MachCSL.Memory.ReadBytes

namespace MachCSL.Logic.TsoPinnedReadWP
open MachCSL.Memory MachCSL.Machine

/-- A single view supplies every byte of one actual word, including n=0. -/
theorem assemble_allowed (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat)
    (sets : Nat → Tso.ByteSet) (view : Nat)
    (bytes : ∀ j, j < n → ∃ byte,
      read g.image g.log (hartAgent cpu) view (addressAdd a j) = some byte ∧ byte ∈ sets j) :
    ∃ word : BitVec (8 * n), ReadsBytes g.image g.log (hartAgent cpu) view a n word ∧ Allowed n sets word := by
  classical
  let chosen (i : Fin n) : Byte := Classical.choose (bytes i.val i.isLt)
  let gathered := List.ofFn chosen
  let word := BitVec.ofNat (8 * n) (assembleBytes gathered)
  have nth (j : Nat) (hj : j < n) : nthByte word j = chosen ⟨j, hj⟩ := by
    dsimp only [word]
    rw [nthByte_assemble_len (8 * n) gathered j (by simp [gathered]) (by simpa [gathered] using hj)]
    simp [gathered]
  refine ⟨word, ?_, ?_⟩
  · intro j hj
    rw [nth j hj]
    exact (Classical.choose_spec (bytes j hj)).1
  · intro j hj
    rw [nth j hj]
    exact (Classical.choose_spec (bytes j hj)).2

theorem slot_reads_words (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat)
    (sets : Nat → Tso.ByteSet) (reads : TsoPinnedRead.SlotReads g cpu a n sets) :
    ∀ view, g.views cpu ≤ view → ∃ word : BitVec (8 * n),
      ReadsBytes g.image g.log (hartAgent cpu) view a n word ∧ Allowed n sets word := by
  intro view lower
  exact assemble_allowed g cpu a n sets view (reads view lower)

end MachCSL.Logic.TsoPinnedReadWP
