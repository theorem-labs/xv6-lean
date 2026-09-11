import MachCSL.Machine.SpinlockPoolUpdateTransports
import MachCSL.Logic.BarrierWPProofs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

theorem winning_advance {g : State} {cpu : CPU} {B view : Nat}
    (winning : Winning g cpu B) (lower : g.views cpu ≤ view) :
    Winning (TsoRead.advanceView g cpu view) cpu B := by
  refine ⟨winning.1, ?_, winning.2.2⟩
  simpa [TsoRead.advanceView, updateHart] using Nat.le_trans winning.2.1 lower

theorem held_advance {g : State} {w : Words} {cpu : CPU} {B v t view}
    (held : HeldFacts g w cpu B v t) (lower : g.views cpu ≤ view) :
    HeldFacts (TsoRead.advanceView g cpu view) w cpu B v t :=
  ⟨held.1, held.2.1, held.2.2.1, winning_advance held.2.2.2 lower⟩

theorem phase_advance {g : State} {w : Words} {cpu : CPU} {c : Cursor} {view : Nat}
    (ok : PhaseOK g w cpu c) (lower : g.views cpu ≤ view) :
    PhaseOK (TsoRead.advanceView g cpu view) w cpu c := by
  cases phase : c.phase with
  | idle => simp only [PhaseOK, phase]
  | reserved old => simpa only [PhaseOK, phase] using ok
  | held B v t =>
    simp only [PhaseOK, phase] at ok ⊢
    exact ⟨held_advance ok.1 lower, ok.2⟩
  | loaded B v t =>
    simp only [PhaseOK, phase] at ok ⊢
    exact ⟨held_advance ok.1 lower, ok.2⟩
  | stored B v t =>
    simp only [PhaseOK, phase] at ok ⊢
    exact held_advance ok lower

theorem counter_not_code (i : Fin 17) (word : BitVec 32) :
    ¬SpinlockFetch.CodeRead i 4 counterRead word := by
  intro allowed
  have address := congrArg BitVec.toNat allowed.2.1
  change SpinlockImage.counterAddress.toNat = (SpinlockImage.instructionAddress i).toNat at address
  rw [SpinlockImage.instruction_address] at address
  change 0x80001004 = 0x80000000 + 4 * i.val at address
  have bound := i.isLt
  omega

theorem lock_not_code (i : Fin 17) (word : BitVec 32) :
    ¬SpinlockFetch.CodeRead i 4 lockRead word := by
  intro allowed
  have address := congrArg BitVec.toNat allowed.2.1
  change SpinlockImage.lockAddress.toNat = (SpinlockImage.instructionAddress i).toNat at address
  rw [SpinlockImage.instruction_address] at address
  change 0x80001000 = 0x80000000 + 4 * i.val at address
  have bound := i.isLt
  omega

/-- Every actual code-read view returns the immutable image instruction and
advances the physical view. No timestamp-zero surrogate is used. -/
theorem code_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (w : Words) (words : WordsOK g w) (ok : PhaseOK g w cpu c)
    (image : g.image = loadedRam SpinlockImage.image)
    (code : SpinlockCodeIntegrity.CodeUnwritten g.log)
    (n : Nat) (req : ReadRequest n) (expected : BitVec (8 * n))
    (allowed : SpinlockFetch.CodeRead c.fetch n req expected)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    (k : MemoryReadWP.ReadResult n → SailM Unit)
    (control : CursorControl g cpu (.impure (.readMem n req) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.readMem n req) k))
      g observations e' g' forks) :
    ∃ view, g.views cpu ≤ view ∧ view ≤ g.log.length ∧
      g' = TsoRead.advanceView g cpu view ∧ e' = .hart gen cpu (k (.Ok (expected, none))) ∧ forks = [] ∧
      Transition (.hart gen cpu (.impure (.readMem n req) k), .hart c) g observations
        (.hart gen cpu (k (.Ok (expected, none))), .hart c) g' [] ∧
      CursorControl g' cpu (k (.Ok (expected, none))) c ∧ PhaseOK g' w cpu c ∧ WordsOK g' w := by
  obtain ⟨rfl, address, expectedEq⟩ := allowed
  have expectedSame : expected = SpinlockImage.word c.fetch := by simpa using expectedEq
  clear expectedEq
  subst expected
  have rest : Plan (SpinlockFetch.CodeRead c.fetch) relations c.registers c.reservation c.phase
      (k (.Ok (SpinlockImage.word c.fetch, none)))
      (fun _ after _ next => ∃ i, SpinlockFamily.Family cpu i after next) := by
    cases EventPlanHead.head_of_plan control.2.2 with
    | codeRead _ _ found rest =>
      have same := found.2.2
      simp only [BitVec.ofNat_toNat] at same
      simpa [same] using rest
    | plain enabled _ _ rest =>
      obtain ⟨word, next, related⟩ := enabled
      generalize oldPhase : c.phase = s at related
      cases related
      exact False.elim (counter_not_code c.fetch (SpinlockImage.word c.fetch) ⟨rfl, address, by simp⟩)
    | exclusive _ _ kind _ => rw [plain] at kind; contradiction
  obtain ⟨view, word, lower, upper, read, rfl, rfl, rfl, rfl⟩ :=
    MemoryReadWP.plain_step_inv _ g gen cpu 4 req k ram plain live observations e' g' forks step
  have expectedRead : ReadsBytes g.image g.log (hartAgent cpu) view req.pa 4 (SpinlockImage.word c.fetch) := by
    rw [image, address]
    exact SpinlockCodeIntegrity.read_code g.log code (hartAgent cpu) view c.fetch
  have same := MemoryReadWP.readsBytes_unique read expectedRead
  subst word
  exact ⟨view, lower, upper, rfl, rfl, rfl,
    .hart live (.codeRead c 4 req _ k ⟨rfl, address, by simp⟩ ram plain)
      (by simp [nextCursor, plain, show ∃ word, SpinlockFetch.CodeRead c.fetch 4 req word from
        ⟨SpinlockImage.word c.fetch, rfl, address, by simp⟩]),
    ⟨control.1, control.2.1, rest⟩, phase_advance ok lower, words⟩

theorem counter_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (w : Words) (words : WordsOK g w) (ok : PhaseOK g w cpu c)
    (B : Nat) (v : BitVec 32) (t : Nat) (phase : c.phase = .held B v t)
    (k : MemoryReadWP.ReadResult 4 → SailM Unit)
    (control : CursorControl g cpu (.impure (.readMem 4 counterRead) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.readMem 4 counterRead) k))
      g observations e' g' forks) :
    ∃ view, g.views cpu ≤ view ∧ view ≤ g.log.length ∧
      g' = TsoRead.advanceView g cpu view ∧ e' = .hart gen cpu (k (.Ok (v, none))) ∧ forks = [] ∧
      Transition (.hart gen cpu (.impure (.readMem 4 counterRead) k), .hart c) g observations
        (.hart gen cpu (k (.Ok (v, none))), .hart { c with phase := .loaded B v t }) g' [] ∧
      CursorControl g' cpu (k (.Ok (v, none))) { c with phase := .loaded B v t } ∧
      PhaseOK g' w cpu { c with phase := .loaded B v t } ∧ WordsOK g' w := by
  have held : HeldFacts g w cpu B v t ∧ t ≤ B := by simpa only [PhaseOK, phase] using ok
  cases EventPlanHead.head_of_plan control.2.2 with
  | codeRead _ _ allowed _ => exact False.elim (counter_not_code c.fetch _ allowed)
  | exclusive _ _ kind _ => contradiction
  | plain enabled ram plain rest =>
    obtain ⟨view, word, lower, upper, read, rfl, rfl, rfl, rfl⟩ :=
      MemoryReadWP.plain_step_inv _ g gen cpu 4 counterRead k ram plain live observations e' g' forks step
    have latest : LatestWord g SpinlockImage.counterAddress v t := by
      rw [← held.1.2.1, ← held.1.2.2.1]
      exact words.2
    have bound := Nat.le_trans held.2 (Nat.le_trans held.1.2.2.2.2.1 lower)
    have same := MemoryReadWP.readsBytes_unique read (latest_word_read latest cpu view bound)
    subst word
    have related : relations.plain c.phase 4 counterRead v (.loaded B v t) := by
      rw [phase]; exact PlainStep.load B v t
    refine ⟨view, lower, upper, rfl, rfl, rfl,
      .hart live (.plain c 4 counterRead v (.loaded B v t) k related ram plain) ?_,
      ⟨control.1, control.2.1, rest _ _ related⟩, ⟨held_advance held.1 lower, held.2⟩, words⟩
    simp [nextCursor, plain, phase, counter_not_code]

theorem fence_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (w : Words) (words : WordsOK g w) (ok : PhaseOK g w cpu c)
    (k : Unit → SailM Unit)
    (control : CursorControl g cpu (.impure (.barrier .Barrier_RISCV_rw_w) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.barrier .Barrier_RISCV_rw_w) k))
      g observations e' g' forks) :
    e' = .hart gen cpu (k ()) ∧ g' = g ∧ forks = [] ∧
      Transition (.hart gen cpu (.impure (.barrier .Barrier_RISCV_rw_w) k), .hart c) g observations
        (.hart gen cpu (k ()), .hart c) g' [] ∧
      CursorControl g' cpu (k ()) c ∧ PhaseOK g' w cpu c ∧ WordsOK g' w := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    BarrierWP.barrier_step_unique _ g gen cpu _ k live observations e' g' forks step
  rw [BarrierWP.afterBarrier_nondraining g cpu _ rfl]
  obtain ⟨enabled, rest⟩ := EventPlanHead.barrier_cases control.2.2
  obtain ⟨next, related⟩ := enabled
  generalize phase : c.phase = s at related
  cases related with
  | fence B v t =>
    have samePhase : relations.barrier c.phase .Barrier_RISCV_rw_w c.phase := by
      rw [phase]; exact BarrierStep.fence B v t
    refine ⟨rfl, rfl, rfl, .hart live (.barrier c _ c.phase k samePhase) ?_,
      ⟨control.1, control.2.1, rest _ samePhase⟩, ok, words⟩
    simp [nextCursor, phase]

end MachCSL.Machine.SpinlockPool
