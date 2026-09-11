import MachCSL.Machine.SpinlockAccessProofs
import MachCSL.Logic.EventPlanCombinators

/-! Actual interruptible data boundaries. Pure branch relations are parameters;
resource-level use must provide the native EventPlan.Access transformations. -/
namespace MachCSL.Machine.SpinlockAccess
open LeanPaperStock.Functions MachCSL.Memory
open MachCSL.Logic.EventPlan
open _root_.Sail.ConcurrencyInterfaceV1.Free

variable {S : Type} (reads : Logic.EventWP.ReadAllowed) (rel : Relations S)
set_option maxRecDepth 100000
set_option maxHeartbeats 100000

def readEnabled (s : S) (location : Location) (exclusive : Bool) : Prop :=
  if exclusive then rel.exclusiveEnabled s 4 (readRequest location exclusive)
  else rel.plainEnabled s 4 (readRequest location exclusive)

def readStep (s : S) (location : Location) (exclusive : Bool) (word : BitVec 32) (next : S) : Prop :=
  if exclusive then rel.exclusive s 4 (readRequest location exclusive) word next
  else rel.plain s 4 (readRequest location exclusive) word next

def readReservation (rr : Option Reservation) (location : Location)
    (exclusive : Bool) (word : BitVec 32) : Option Reservation :=
  if exclusive then some (snapshot (address location) 4 word) else rr

/-- Every relation-permitted returned word is retained, with exactly the
reservation produced by this individual memory event. -/
theorem read_ram_event (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (location : Location) (exclusive : Bool) (enabled : readEnabled rel s location exclusive) :
    Plan reads rel rs rr s (read_ram (readKind exclusive) (.Physaddr (address location)) 4 false)
      (fun result after rr' next => after = rs ∧
        rr' = readReservation rr location exclusive result.1 ∧ readStep rel s location exclusive result.1 next) := by
  cases exclusive
  · apply Plan.plain enabled (read_request_ram location false) (read_request_exclusive location false)
    intro word next step
    exact .pure ⟨rfl, rfl, step⟩
  · apply Plan.exclusive enabled (read_request_ram location true) (read_request_exclusive location true)
    intro word next step
    exact .pure ⟨rfl, rfl, step⟩

/-- Ordinary and reservation-backed writes share the real write event. The
mode is an explicit input whose reservation equality is kernel checked. -/
theorem write_ram_event (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (location : Location) (exclusive : Bool) (word : BitVec 32)
    (mode : WriteMode 4 (writeRequest location exclusive word) rr)
    (enabled : rel.writeEnabled s 4 (writeRequest location exclusive word) word)
    (eligible : rel.writeModeEnabled s rr 4 (writeRequest location exclusive word) word mode) :
    Plan reads rel rs rr s (write_ram (writeKind exclusive) (.Physaddr (address location)) 4 word ())
      (fun result after rr' next => result = true ∧ after = rs ∧ rr' = none ∧
        rel.write s 4 (writeRequest location exclusive word) word next) := by
  cases exclusive
  all_goals
    apply Plan.write enabled (show (writeRequest location _ word).value = some word from rfl)
      (write_request_ram location _ word) mode eligible
    intro next step
    exact .pure ⟨rfl, rfl, rfl, step⟩

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
    Plan reads rel rs rr s (program >>= next).run Q :=
  prefix_plan reads rel first rest

/-- The exact physical read operation used by a load or AMOSWAP.aq. -/
def readMode (exclusive : Bool) : Mode := if exclusive then .amo else .load

def readFacts (rel : Relations S) (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (location : Location) (exclusive : Bool) (word : BitVec 32)
    (after : RegisterFile) (rr' : Option Reservation) (next : S) : Prop :=
  after = rs ∧ rr' = readReservation rr location exclusive word ∧ readStep rel s location exclusive word next

private theorem update_word (old word : BitVec 32) :
    Sail.BitVec.updateSubrange old 31 0 word = word := by
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]

/-- Physical reads retain all returned words; the enclosing access proof must
supply the mutable/exclusive callback for the exact generated request. -/
theorem checked_read_plan (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (location : Location) (exclusive : Bool)
    (enabled : readEnabled rel s location exclusive) :
    Plan reads rel rs rr s
      (checked_mem_read (access (readMode exclusive)) .PBMT_PMA .Machine
        (.Physaddr (address location)) 4 exclusive false exclusive false)
      (fun result after rr' next => ∃ word, result = .Ok (word, ()) ∧
        readFacts rel rs rr s location exclusive word after rr' next) := by
  let facts := readFacts rel rs rr s location exclusive
  have hpma := pma_priority_plan reads rs static location (readMode exclusive)
  have hpmp := pmp_plan reads rs off location (readMode exclusive)
  have hmmio := readable_plan reads rs static location
  have hread := read_ram_event reads rel rs rr s location exclusive enabled
  have hkind : Logic.EventWP.Returns reads rs (read_kind_of_flags exclusive false exclusive)
      (readKind exclusive) rs := by
    cases exclusive <;> exact Logic.EventWP.pure_plan reads rs _
  cases location <;> cases exclusive
  all_goals
    unfold checked_mem_read _root_.Sail.SailME.run PreSail.PreSailME.run
    apply Plan.bind (P := fun result after rr' next => ∃ word,
      result = (Except.ok (.Ok (word, ())) : Except
        (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))
        (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))) ∧
      facts word after rr' next)
    · apply prefix_except reads rel (after := rs) (value := accessInfo)
      · refine (hpma.liftExcept (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))).bind (after := rs) ?_
        exact Logic.EventWP.pure_plan reads rs _
      apply prefix_except reads rel (after := rs) (value := ((1, 4) : Int × Int))
        (Logic.EventWP.pure_plan reads rs _)
      apply prefix_except reads rel (after := rs)
        (hkind.liftExcept (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType)))
      apply Plan.bind (P := fun result after rr' next => ∃ word, result =
          (Except.ok (word, true, (0 : Nat)) : Except
            (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))
            (BitVec 32 × Bool × Nat)) ∧ facts word after rr' next)
      · simp only [untilFuelM]
        apply Plan.bind (P := fun result after rr' next => ∃ word, result =
          (Except.ok (word, true, (0 : Nat)) : Except
            (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))
            (BitVec 32 × Bool × Nat)) ∧ facts word after rr' next)
        · apply Plan.bind (P := fun result after rr' next => ∃ word, result =
            (Except.ok (word, true, (0 : Nat)) : Except
              (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))
              (BitVec 32 × Bool × Nat)) ∧ facts word after rr' next)
          · apply prefix_except reads rel (after := rs) (value := ())
            · exact Logic.EventWP.pure_plan reads rs _
            refine prefix_plan reads rel
              (hpmp.liftExcept (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))) ?_
            refine prefix_plan reads rel
              (hmmio.liftExcept (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))) ?_
            simp only [ExceptT.bindCont]
            apply Plan.bind (P := fun result after rr' next => ∃ word, result =
              (Except.ok word : Except (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))
                (BitVec 32)) ∧ facts word after rr' next)
            · refine Plan.bind (hread.liftExcept (_root_.Sail.Result (BitVec 32 × Unit) (physaddr × ExceptionType))) ?_
              rintro _ after rr' next ⟨⟨word, metaValue⟩, rfl, rfl, reservation, step⟩
              cases metaValue
              exact .pure ⟨word, rfl, rfl, reservation, step⟩
            · rintro _ after rr' next ⟨word, rfl, rfl, reservation, step⟩
              apply Plan.pure
              refine ⟨word, ?_, rfl, reservation, step⟩
              change Except.ok (Sail.BitVec.updateSubrange (0#32) 31 0 word, true, (0 : Nat)) = _
              rw [update_word]
          · rintro _ after rr' next ⟨word, rfl, rfl, reservation, step⟩
            exact .pure ⟨word, rfl, rfl, reservation, step⟩
        · rintro _ after rr' next ⟨word, rfl, rfl, reservation, step⟩
          exact .pure ⟨word, rfl, rfl, reservation, step⟩
      · rintro _ after rr' next ⟨word, rfl, rfl, reservation, step⟩
        exact .pure ⟨word, rfl, rfl, reservation, step⟩
    · rintro _ after rr' next ⟨word, rfl, rfl, reservation, step⟩
      exact .pure ⟨word, rfl, rfl, reservation, step⟩

/-- The generated non-MMIO physical read, including privilege register reads
and the exact metadata-dropping wrapper. -/
theorem mem_read_plan (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (location : Location) (exclusive : Bool)
    (enabled : readEnabled rel s location exclusive) :
    Plan reads rel rs rr s
      (mem_read (access (readMode exclusive)) .PBMT_PMA
        (.Physaddr (address location)) 4 exclusive false exclusive)
      (fun result after rr' next => ∃ word, result = .Ok word ∧
        readFacts rel rs rr s location exclusive word after rr' next) := by
  let facts := readFacts rel rs rr s location exclusive
  have hread := checked_read_plan reads rel rs rr s static off location exclusive enabled
  unfold mem_read
  refine prefix_plan reads rel (Logic.EventWP.read_plan reads rs .mstatus (by decide)) ?_
  refine prefix_plan reads rel (Logic.EventWP.read_plan reads rs .cur_privilege (by decide)) ?_
  rw [static.mstatus, static.privilege]
  cases exclusive
  all_goals
    change Plan reads rel rs rr s (mem_read_priv _ .PBMT_PMA .Machine _ 4 _ false _) _
    unfold mem_read_priv
    refine Plan.bind (P := fun result after rr' next => ∃ word, result = .Ok (word, ()) ∧
      facts word after rr' next) ?_ ?_
    · unfold mem_read_priv_meta
      refine Plan.bind hread ?_
      rintro _ after rr' next ⟨word, rfl, facts⟩
      exact .pure ⟨word, rfl, facts⟩
    · rintro _ after rr' next ⟨word, rfl, facts⟩
      exact .pure ⟨word, rfl, facts⟩

/-- Store access metadata, with the conditional AMOSWAP write kept distinct
from the preceding exclusive read. -/
def writeMode (exclusive : Bool) : Mode := if exclusive then .amo else .store

def writeFacts (rel : Relations S) (rs : RegisterFile) (s : S)
    (location : Location) (exclusive : Bool) (word : BitVec 32)
    (after : RegisterFile) (rr' : Option Reservation) (next : S) : Prop :=
  after = rs ∧ rr' = none ∧ rel.write s 4 (writeRequest location exclusive word) word next

private theorem extract_word (word : BitVec 32) :
    Sail.BitVec.extractLsb word 31 0 = word := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']

/-- The generated checked physical write, with exact request, selected
proof-side mode, reservation consumption, and arbitrary stored word. -/
theorem checked_write_plan (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (location : Location) (exclusive : Bool)
    (word : BitVec 32) (mode : WriteMode 4 (writeRequest location exclusive word) rr)
    (enabled : rel.writeEnabled s 4 (writeRequest location exclusive word) word)
    (eligible : rel.writeModeEnabled s rr 4 (writeRequest location exclusive word) word mode) :
    Plan reads rel rs rr s
      (checked_mem_write (.Physaddr (address location)) 4 word (access (writeMode exclusive))
        .PBMT_PMA .Machine () false false exclusive)
      (fun result after rr' next => result = .Ok true ∧
        writeFacts rel rs s location exclusive word after rr' next) := by
  let facts := writeFacts rel rs s location exclusive word
  have hpma := pma_priority_plan reads rs static location (writeMode exclusive)
  have hpmp := pmp_plan reads rs off location (writeMode exclusive)
  have hmmio := writable_plan reads rs static location
  have hwrite := write_ram_event reads rel rs rr s location exclusive word mode enabled eligible
  have hkind : Logic.EventWP.Returns reads rs (write_kind_of_flags false false exclusive)
      (writeKind exclusive) rs := by
    cases exclusive <;> exact Logic.EventWP.pure_plan reads rs _
  cases location <;> cases exclusive
  all_goals
    unfold checked_mem_write _root_.Sail.SailME.run PreSail.PreSailME.run
    apply Plan.bind (P := fun result after rr' next =>
      result = (Except.ok (.Ok true) : Except
        (_root_.Sail.Result Bool (physaddr × ExceptionType))
        (_root_.Sail.Result Bool (physaddr × ExceptionType))) ∧ facts after rr' next)
    · apply prefix_except reads rel (after := rs) (value := accessInfo)
      · refine (hpma.liftExcept (_root_.Sail.Result Bool (physaddr × ExceptionType))).bind (after := rs) ?_
        exact Logic.EventWP.pure_plan reads rs _
      apply prefix_except reads rel (after := rs) (value := ((1, 4) : Int × Int))
        (Logic.EventWP.pure_plan reads rs _)
      apply prefix_except reads rel (after := rs)
        (hkind.liftExcept (_root_.Sail.Result Bool (physaddr × ExceptionType)))
      apply Plan.bind (P := fun result after rr' next => result =
          (Except.ok (true, (0 : Nat), true) : Except
            (_root_.Sail.Result Bool (physaddr × ExceptionType))
            (Bool × Nat × Bool)) ∧ facts after rr' next)
      · simp only [untilFuelM]
        apply Plan.bind (P := fun result after rr' next => result =
          (Except.ok (true, (0 : Nat), true) : Except
            (_root_.Sail.Result Bool (physaddr × ExceptionType))
            (Bool × Nat × Bool)) ∧ facts after rr' next)
        · apply prefix_except reads rel (after := rs) (value := ())
          · exact Logic.EventWP.pure_plan reads rs _
          refine prefix_plan reads rel
            (hpmp.liftExcept (_root_.Sail.Result Bool (physaddr × ExceptionType))) ?_
          apply Plan.bind (P := fun result after rr' next => result =
            (Except.ok true : Except (_root_.Sail.Result Bool (physaddr × ExceptionType)) Bool) ∧
            facts after rr' next)
          · refine prefix_plan reads rel
              (hmmio.liftExcept (_root_.Sail.Result Bool (physaddr × ExceptionType))) ?_
            simp only [ExceptT.bindCont]
            simp only [Bool.false_eq_true, ↓reduceIte]
            change Plan reads rel rs rr s
              (((monadLift (write_ram _ _ 4 (Sail.BitVec.extractLsb word 31 0) ()) :
                SailME (_root_.Sail.Result Bool (physaddr × ExceptionType)) Bool) >>= fun value =>
                  pure (true && value)).run) _
            rw [extract_word]
            refine Plan.bind (hwrite.liftExcept (_root_.Sail.Result Bool (physaddr × ExceptionType))) ?_
            rintro _ after rr' next ⟨value, rfl, rfl, rfl, reservation, step⟩
            exact .pure ⟨rfl, rfl, reservation, step⟩
          · rintro _ after rr' next ⟨rfl, facts⟩
            exact .pure ⟨rfl, facts⟩
        · rintro _ after rr' next ⟨rfl, facts⟩
          exact .pure ⟨rfl, facts⟩
      · rintro _ after rr' next ⟨rfl, facts⟩
        exact .pure ⟨rfl, facts⟩
    · rintro _ after rr' next ⟨rfl, facts⟩
      exact .pure ⟨rfl, facts⟩

/-- Actual privilege reads and callback wrapper around the checked write. -/
theorem mem_write_plan (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (location : Location) (exclusive : Bool)
    (word : BitVec 32) (mode : WriteMode 4 (writeRequest location exclusive word) rr)
    (enabled : rel.writeEnabled s 4 (writeRequest location exclusive word) word)
    (eligible : rel.writeModeEnabled s rr 4 (writeRequest location exclusive word) word mode) :
    Plan reads rel rs rr s
      (mem_write_value (.Physaddr (address location)) 4 word (access (writeMode exclusive))
        .PBMT_PMA false false exclusive)
      (fun result after rr' next => result = .Ok true ∧
        writeFacts rel rs s location exclusive word after rr' next) := by
  have hwrite := checked_write_plan reads rel rs rr s static off location exclusive word mode enabled eligible
  unfold mem_write_value mem_write_value_meta
  refine prefix_plan reads rel (Logic.EventWP.read_plan reads rs .mstatus (by decide)) ?_
  refine prefix_plan reads rel (Logic.EventWP.read_plan reads rs .cur_privilege (by decide)) ?_
  rw [static.mstatus, static.privilege]
  cases exclusive
  all_goals
    change Plan reads rel rs rr s (mem_write_value_priv_meta _ 4 word _ .PBMT_PMA .Machine () false false _) _
    unfold mem_write_value_priv_meta
    refine Plan.bind hwrite ?_
    rintro _ after rr' next ⟨rfl, facts⟩
    exact .pure ⟨rfl, facts⟩

end MachCSL.Machine.SpinlockAccess
