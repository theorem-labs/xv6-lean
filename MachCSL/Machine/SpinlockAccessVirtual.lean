import MachCSL.Machine.SpinlockAccessPlans

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

private theorem update_word (old word : BitVec 32) :
    Sail.BitVec.updateSubrange old 31 0 word = word := by
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]

private theorem extract_word (word : BitVec 32) :
    Sail.BitVec.extractLsb word 31 0 = word := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']

/-- No virtual translation or exception is elided: this composes the exact
M-mode translation and the generated physical read. -/
theorem translate_read_plan (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (location : Location)
    (enabled : readEnabled rel s location false) :
    Plan reads rel rs rr s
      (translate_and_read_value (.Virtaddr (address location)) 4 (.Load .Data) false false false)
      (fun result after rr' next => ∃ word, result = .Ok (.Physaddr (address location), word) ∧
        readFacts rel rs rr s location false word after rr' next) := by
  unfold translate_and_read_value
  refine prefix_plan reads rel (translate_plan reads rs static location .load) ?_
  refine Plan.bind (mem_read_plan reads rel rs rr s static off location false enabled) ?_
  rintro _ after rr' next ⟨word, rfl, facts⟩
  exact .pure ⟨word, rfl, facts⟩

/-- Aligned four-byte LW addresses do not cross a page. -/
theorem split_page_plan (rs : RegisterFile) (location : Location) :
    Logic.EventWP.Returns reads rs (split_on_page_boundary (address location) 4) (4, 0) rs := by
  cases location <;> exact Logic.EventWP.pure_plan reads rs _

theorem vmem_read_addr_plan (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (location : Location)
    (enabled : readEnabled rel s location false) :
    Plan reads rel rs rr s
      (vmem_read_addr (.Virtaddr (address location)) 4 (.Load .Data) false false false)
      (fun result after rr' next => ∃ word, result = .Ok word ∧
        readFacts rel rs rr s location false word after rr' next) := by
  let facts := readFacts rel rs rr s location false
  have hread := translate_read_plan reads rel rs rr s static off location enabled
  have hsplit := split_page_plan reads rs location
  unfold vmem_read_addr _root_.Sail.SailME.run PreSail.PreSailME.run
  apply Plan.bind (P := fun result after rr' next => ∃ word,
    result = (Except.ok (.Ok word) : Except (_root_.Sail.Result (BitVec 32) ExecutionResult)
      (_root_.Sail.Result (BitVec 32) ExecutionResult)) ∧ facts word after rr' next)
  · simp only [address_aligned, LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine prefix_plan reads rel (hsplit.liftExcept (_root_.Sail.Result (BitVec 32) ExecutionResult)) ?_
    refine prefix_plan reads rel ((Logic.EventWP.read_plan reads rs .mstatus (by decide)).liftExcept (_root_.Sail.Result (BitVec 32) ExecutionResult)) ?_
    refine prefix_plan reads rel ((Logic.EventWP.read_plan reads rs .cur_privilege (by decide)).liftExcept (_root_.Sail.Result (BitVec 32) ExecutionResult)) ?_
    rw [static.mstatus, static.privilege]
    apply prefix_except reads rel (after := rs) (value := .Machine)
    · exact Logic.EventWP.pure_plan reads rs _
    apply prefix_except reads rel (after := rs) (value := false)
    · exact Logic.EventWP.pure_plan reads rs _
    apply prefix_except reads rel (after := rs) (value := 0#32)
    · exact Logic.EventWP.pure_plan reads rs _
    apply Plan.bind (P := fun result after rr' next => ∃ word,
      result = (Except.ok word : Except (_root_.Sail.Result (BitVec 32) ExecutionResult) (BitVec 32)) ∧
      facts word after rr' next)
    · refine Plan.bind (hread.liftExcept (_root_.Sail.Result (BitVec 32) ExecutionResult)) ?_
      rintro _ after rr' next ⟨_, rfl, word, rfl, facts⟩
      apply Plan.pure
      refine ⟨word, ?_, facts⟩
      change Except.ok (Sail.BitVec.updateSubrange (0#32) 31 0 word) = Except.ok word
      rw [update_word]
    · rintro _ after rr' next ⟨word, rfl, facts⟩
      exact .pure ⟨word, rfl, facts⟩
  · rintro _ after rr' next ⟨word, rfl, facts⟩
    exact .pure ⟨word, rfl, facts⟩

/-- Full generated virtual load, including the x10 operand/address transform. -/
theorem vmem_read_plan (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (base : rs .x10 = SpinlockImage.lockAddress)
    (location : Location) (enabled : readEnabled rel s location false) :
    Plan reads rel rs rr s
      (vmem_read (.Regidx 10#5) (offset location) 4 (.Load .Data) false false false)
      (fun result after rr' next => ∃ word, result = .Ok word ∧
        readFacts rel rs rr s location false word after rr' next) := by
  let facts := readFacts rel rs rr s location false
  have haddr := transform_plan reads rs static base location .load
  have hread := vmem_read_addr_plan reads rel rs rr s static off location enabled
  unfold vmem_read _root_.Sail.SailME.run PreSail.PreSailME.run
  apply Plan.bind (P := fun result after rr' next => ∃ word,
    result = (Except.ok (.Ok word) : Except (_root_.Sail.Result (BitVec 32) ExecutionResult)
      (_root_.Sail.Result (BitVec 32) ExecutionResult)) ∧ facts word after rr' next)
  · apply prefix_except reads rel (after := rs) (value := (.Virtaddr (address location)))
    · refine (haddr.liftExcept (_root_.Sail.Result (BitVec 32) ExecutionResult)).bind (after := rs) ?_
      exact Logic.EventWP.pure_plan reads rs _
    exact (hread.liftExcept (_root_.Sail.Result (BitVec 32) ExecutionResult)).mono
      fun result after rr' next ⟨value, hv, word, hw, hf⟩ => ⟨word, hv.trans (congrArg Except.ok hw), hf⟩
  · rintro _ after rr' next ⟨word, rfl, hf⟩
    exact .pure ⟨word, rfl, hf⟩

/-- The virtual plain-store path retains the actual EA announcement, full
word extraction, conditional-kind assertion, and physical write event. -/
theorem vmem_write_addr_plan [Platform] (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (location : Location) (word : BitVec 32)
    (enabled : rel.writeEnabled s 4 (writeRequest location false word) word)
    (eligible : rel.writeModeEnabled s rr 4 (writeRequest location false word) word .ordinary) :
    Plan reads rel rs rr s
      (vmem_write_addr (.Virtaddr (address location)) 4 word (.Store .Data) false false false)
      (fun result after rr' next => result = .Ok true ∧
        writeFacts rel rs s location false word after rr' next) := by
  let facts := writeFacts rel rs s location false word
  have hsplit := split_page_plan reads rs location
  have htranslate := translate_plan reads rs static location .store
  have hea := write_ea_plan reads rs static off location .store
  have hwrite := mem_write_plan reads rel rs rr s static off location false word .ordinary enabled eligible
  unfold vmem_write_addr _root_.Sail.SailME.run PreSail.PreSailME.run
  apply Plan.bind (P := fun result after rr' next =>
    result = (Except.ok (.Ok true) : Except (_root_.Sail.Result Bool ExecutionResult)
      (_root_.Sail.Result Bool ExecutionResult)) ∧ facts after rr' next)
  · simp only [address_aligned, LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine prefix_plan reads rel (hsplit.liftExcept (_root_.Sail.Result Bool ExecutionResult)) ?_
    refine prefix_plan reads rel ((Logic.EventWP.read_plan reads rs .mstatus (by decide)).liftExcept (_root_.Sail.Result Bool ExecutionResult)) ?_
    refine prefix_plan reads rel ((Logic.EventWP.read_plan reads rs .cur_privilege (by decide)).liftExcept (_root_.Sail.Result Bool ExecutionResult)) ?_
    rw [static.mstatus, static.privilege]
    apply prefix_except reads rel (after := rs) (value := .Machine)
    · exact Logic.EventWP.pure_plan reads rs _
    apply prefix_except reads rel (after := rs) (value := false)
    · exact Logic.EventWP.pure_plan reads rs _
    apply prefix_except reads rel (after := rs) (value := true)
    · exact Logic.EventWP.pure_plan reads rs _
    apply Plan.bind (P := fun result after rr' next =>
      result = (Except.ok true : Except (_root_.Sail.Result Bool ExecutionResult) Bool) ∧
      facts after rr' next)
    · refine prefix_plan reads rel (htranslate.liftExcept (_root_.Sail.Result Bool ExecutionResult)) ?_
      apply prefix_except reads rel (after := rs) (value := ())
      · exact Logic.EventWP.pure_plan reads rs _
      refine prefix_plan reads rel (hea.liftExcept (_root_.Sail.Result Bool ExecutionResult)) ?_
      simp only [ExceptT.bindCont]
      change Plan reads rel rs rr s
        (((monadLift (mem_write_value (.Physaddr (address location)) 4
            (Sail.BitVec.extractLsb word 31 0) (.Store .Data) .PBMT_PMA false false false) :
          SailME (_root_.Sail.Result Bool ExecutionResult) (_root_.Sail.Result Bool (physaddr × ExceptionType))) >>= _).run) _
      rw [extract_word]
      refine Plan.bind (hwrite.liftExcept (_root_.Sail.Result Bool ExecutionResult)) ?_
      rintro _ after rr' next ⟨_, rfl, rfl, hf⟩
      exact .pure ⟨rfl, hf⟩
    · rintro _ after rr' next ⟨rfl, hf⟩
      exact .pure ⟨rfl, hf⟩
  · rintro _ after rr' next ⟨rfl, hf⟩
    exact .pure ⟨rfl, hf⟩

/-- Full generated virtual store, including the x10 address transform. -/
theorem vmem_write_plan [Platform] (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (base : rs .x10 = SpinlockImage.lockAddress)
    (location : Location) (word : BitVec 32)
    (enabled : rel.writeEnabled s 4 (writeRequest location false word) word)
    (eligible : rel.writeModeEnabled s rr 4 (writeRequest location false word) word .ordinary) :
    Plan reads rel rs rr s
      (vmem_write (.Regidx 10#5) (offset location) 4 word (.Store .Data) false false false)
      (fun result after rr' next => result = .Ok true ∧
        writeFacts rel rs s location false word after rr' next) := by
  let facts := writeFacts rel rs s location false word
  have haddr := transform_plan reads rs static base location .store
  have hwrite := vmem_write_addr_plan reads rel rs rr s static off location word enabled eligible
  unfold vmem_write _root_.Sail.SailME.run PreSail.PreSailME.run
  apply Plan.bind (P := fun result after rr' next =>
    result = (Except.ok (.Ok true) : Except (_root_.Sail.Result Bool ExecutionResult)
      (_root_.Sail.Result Bool ExecutionResult)) ∧ facts after rr' next)
  · apply prefix_except reads rel (after := rs) (value := (.Virtaddr (address location)))
    · refine (haddr.liftExcept (_root_.Sail.Result Bool ExecutionResult)).bind (after := rs) ?_
      exact Logic.EventWP.pure_plan reads rs _
    exact (hwrite.liftExcept (_root_.Sail.Result Bool ExecutionResult)).mono
      fun result after rr' next ⟨value, hv, hw, hf⟩ => ⟨hv.trans (congrArg Except.ok hw), hf⟩
  · rintro _ after rr' next ⟨rfl, hf⟩
    exact .pure ⟨rfl, hf⟩

end MachCSL.Machine.SpinlockAccess
