import MachCSL.Machine.SpinlockAccessPlans
import MachCSL.Machine.SpinlockDecodeDefs

namespace MachCSL.Machine.SpinlockAccess
open LeanPaperStock.Functions MachCSL.Memory MachCSL.Logic.EventPlan
open _root_.Sail.ConcurrencyInterfaceV1.Free
variable {S : Type} (reads : Logic.EventWP.ReadAllowed) (rel : Relations S)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem prefix_plan {α β : Type} {rs rr s after}
    {program : SailM α} {next : α → SailM β} {value : α}
    {Q : β → RegisterFile → Option Reservation → S → Prop}
    (first : Logic.EventWP.Returns reads rs program value after)
    (rest : Plan reads rel after rr s (next value) Q) :
    Plan reads rel rs rr s (program >>= next) Q :=
  .prefix first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem prefix_except {ε α β : Type} {rs rr s after}
    {program : SailME ε α} {next : α → SailME ε β} {value Q}
    (first : Logic.EventWP.Returns reads rs program.run (.ok value) after)
    (rest : Plan reads rel after rr s (next value).run Q) :
    Plan reads rel rs rr s (program >>= next).run Q := prefix_plan reads rel first rest

def amoWord (rs : RegisterFile) : BitVec 32 := Sail.BitVec.extractLsb (rs .x15) 31 0

def amoAfter (rs : RegisterFile) (old : BitVec 32) : RegisterFile :=
  Sail.Registers.write rs .x15 (sign_extend (m := 64) old)

def amoMode (word old : BitVec 32) :
    WriteMode 4 (writeRequest .lock true word) (some (snapshot (address .lock) 4 old)) :=
  .reserved old rfl (by decide)

def amoFacts (rel : Relations S) (rs : RegisterFile) (s : S)
    (after : RegisterFile) (rr' : Option Reservation) (next : S) : Prop :=
  ∃ old middle, after = amoAfter rs old ∧ rr' = none ∧
    rel.exclusive s 4 (readRequest .lock true) old middle ∧
    rel.write middle 4 (writeRequest .lock true (amoWord rs)) (amoWord rs) next

private theorem rx15_plan (rs : RegisterFile) :
    Logic.EventWP.Returns reads rs (rX_bits (.Regidx 15#5)) (rs .x15) rs := by
  exact (Logic.EventWP.read_plan reads rs .x15 (by decide)).bind
    (Logic.EventWP.pure_plan reads rs _)

private theorem wx15_plan (rs : RegisterFile) (word : BitVec 32) :
    Logic.EventWP.Returns reads rs (wX_bits (.Regidx 15#5) (sign_extend (m := 64) word))
      () (amoAfter rs word) := by
  exact (Logic.EventWP.write_plan reads rs .x15 (sign_extend (m := 64) word) (by decide)).bind
    (Logic.EventWP.pure_plan reads _ _)

/-- The actual AMOSWAP.W.aq instruction has two distinct memory boundaries.
The successor relation supplies eligibility for its reservation-backed write;
no read value or protocol transition is chosen by this proof. -/
theorem amo_plan [Platform] (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (base : rs .x10 = SpinlockImage.lockAddress)
    (enabled : rel.exclusiveEnabled s 4 (readRequest .lock true))
    (writeEnabled : ∀ old middle, rel.exclusive s 4 (readRequest .lock true) old middle →
      rel.writeEnabled middle 4 (writeRequest .lock true (amoWord rs)) (amoWord rs))
    (eligible : ∀ old middle, rel.exclusive s 4 (readRequest .lock true) old middle →
      rel.writeModeEnabled middle (some (snapshot (address .lock) 4 old)) 4
        (writeRequest .lock true (amoWord rs)) (amoWord rs) (amoMode (amoWord rs) old)) :
    Plan reads rel rs rr s (execute_AMO .AMOSWAP true false (.Regidx 15#5) (.Regidx 10#5) 4 (.Regidx 15#5))
      (fun result after rr' next => result = .Retire_Success () ∧ amoFacts rel rs s after rr' next) := by
  have haddr := transform_plan reads rs static base .lock .amo
  have htranslate := translate_plan reads rs static .lock .amo
  have hea := write_ea_plan reads rs static off .lock .amo
  have hread := mem_read_plan reads rel rs rr s static off .lock true enabled
  unfold execute_AMO _root_.Sail.SailME.run PreSail.PreSailME.run
  apply Plan.bind (P := fun result after rr' next =>
    result = (Except.ok (.Retire_Success ()) : Except ExecutionResult ExecutionResult) ∧
    amoFacts rel rs s after rr' next)
  · apply prefix_except reads rel (after := rs) (value := ())
    · exact Logic.EventWP.pure_plan reads rs _
    apply prefix_except reads rel (after := rs) (value := (.Virtaddr (address .lock)))
    · refine (haddr.liftExcept ExecutionResult).bind (after := rs) ?_
      exact Logic.EventWP.pure_plan reads rs _
    simp only [address_aligned, LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    apply prefix_except reads rel (after := rs) (value := ((.Physaddr (address .lock)), .PBMT_PMA))
    · refine (htranslate.liftExcept ExecutionResult).bind (after := rs) ?_
      exact Logic.EventWP.pure_plan reads rs _
    apply Plan.bind (P := fun result after rr' next => ∃ old, result = (Except.ok old : Except ExecutionResult (BitVec 32)) ∧
      readFacts rel rs rr s .lock true old after rr' next)
    · refine prefix_plan reads rel (hea.liftExcept ExecutionResult) ?_
      refine Plan.bind (hread.liftExcept ExecutionResult) ?_
      rintro _ after rr' next ⟨_, rfl, old, rfl, facts⟩
      exact .pure ⟨old, rfl, facts⟩
    · rintro _ after rr' middle ⟨old, rfl, hafter, hrr, readStep⟩
      subst after
      subst rr'
      apply prefix_except reads rel (after := rs) (value := amoWord rs)
      · refine ((rx15_plan reads rs).liftExcept ExecutionResult).bind (after := rs) ?_
        exact Logic.EventWP.pure_plan reads rs _
      with_unfolding_all
        refine prefix_plan reads rel ((rx15_plan reads rs).liftExcept ExecutionResult) ?_
      simp only [ExceptT.bindCont]
      apply prefix_except reads rel (after := rs) (value := amoWord rs)
      · exact Logic.EventWP.pure_plan reads rs _
      have hwrite0 := mem_write_plan reads rel rs (some (snapshot (address .lock) 4 old)) middle
        static off .lock true (amoWord rs) (amoMode (amoWord rs) old)
        (writeEnabled old middle readStep) (eligible old middle readStep)
      have hwrite : Plan reads rel rs (some (snapshot (address .lock) 4 old)) middle
          (mem_write_value (.Physaddr (address .lock)) 4 (sign_extend (m := 32) (amoWord rs))
            (access .amo) .PBMT_PMA false false true)
          (fun result after rr' next => result = .Ok true ∧
            writeFacts rel rs middle .lock true (amoWord rs) after rr' next) := by
        simpa only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq, writeMode, Bool.true_eq, ↓reduceIte] using hwrite0
      have cas : (amoop.AMOSWAP == amoop.AMOCAS) = false := rfl
      simp only [cas, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      refine Plan.bind (hwrite.liftExcept ExecutionResult) ?_
      rintro _ after rr' next ⟨_, rfl, rfl, hafter, hrr, writeStep⟩
      subst after
      subst rr'
      refine prefix_plan reads rel ((wx15_plan reads rs old).liftExcept ExecutionResult) ?_
      exact .pure ⟨rfl, old, middle, rfl, rfl, readStep, writeStep⟩
  · rintro _ after rr' next ⟨rfl, facts⟩
    exact .pure ⟨rfl, facts⟩

/-- The release-side FENCE rw,w is the actual non-draining fence event. -/
theorem fence_plan [Platform] (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (privilege : rs .cur_privilege = .Machine)
    (enabled : rel.barrierEnabled s .Barrier_RISCV_rw_w) :
    Plan reads rel rs rr s (execute_FENCE 0#4 3#4 1#4 (.Regidx 0#5) (.Regidx 0#5))
      (fun result after rr' next => result = .Retire_Success () ∧ after = rs ∧ rr' = rr ∧
        rel.barrier s .Barrier_RISCV_rw_w next) := by
  have fiom : Logic.EventWP.Returns reads rs (is_fiom_active ()) false rs := by
    unfold is_fiom_active
    refine (Logic.EventWP.read_plan reads rs .cur_privilege (by decide)).bind ?_
    rw [privilege]
    exact Logic.EventWP.pure_plan reads rs _
  unfold execute_FENCE
  refine prefix_plan reads rel fiom ?_
  apply Plan.barrier enabled
  intro next step
  exact .pure ⟨rfl, rfl, rfl, step⟩

theorem fence_nondraining : fenceDrains .Barrier_RISCV_rw_w = false := rfl

end MachCSL.Machine.SpinlockAccess
