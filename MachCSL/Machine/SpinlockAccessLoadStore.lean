import MachCSL.Machine.SpinlockAccessVirtual
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

def loadAfter (rs : RegisterFile) (word : BitVec 32) : RegisterFile :=
  Sail.Registers.write rs .x16 (sign_extend (m := 64) word)

def storeWord (rs : RegisterFile) : BitVec 32 := Sail.BitVec.extractLsb (rs .x16) 31 0

private theorem wx16_plan (rs : RegisterFile) (word : BitVec 32) :
    Logic.EventWP.Returns reads rs (wX_bits (.Regidx 16#5) (sign_extend (m := 64) word))
      () (loadAfter rs word) := by
  exact (Logic.EventWP.write_plan reads rs .x16 (sign_extend (m := 64) word) (by decide)).bind
    (Logic.EventWP.pure_plan reads _ _)

private theorem rx16_plan (rs : RegisterFile) :
    Logic.EventWP.Returns reads rs (rX_bits (.Regidx 16#5)) (rs .x16) rs := by
  exact (Logic.EventWP.read_plan reads rs .x16 (by decide)).bind
    (Logic.EventWP.pure_plan reads rs _)

/-- Actual LW counter+4, preserving every possible read value and its plain
read relation before sign-extending into x16. -/
theorem load_plan [Platform] (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (base : rs .x10 = SpinlockImage.lockAddress)
    (enabled : rel.plainEnabled s 4 (readRequest .counter false)) :
    Plan reads rel rs rr s (execute_LOAD 4#12 (.Regidx 10#5) (.Regidx 16#5) false 4)
      (fun result after rr' next => ∃ word, result = .Retire_Success () ∧
        after = loadAfter rs word ∧ rr' = rr ∧ rel.plain s 4 (readRequest .counter false) word next) := by
  have hread := vmem_read_plan reads rel rs rr s static off base .counter enabled
  unfold execute_LOAD
  apply prefix_plan reads rel (after := rs) (value := ())
  · exact Logic.EventWP.pure_plan reads rs _
  refine Plan.bind hread ?_
  rintro _ after rr' next ⟨word, rfl, hafter, hrr, step⟩
  subst after
  subst rr'
  refine prefix_plan reads rel (wx16_plan reads rs word) ?_
  exact .pure ⟨word, rfl, rfl, rfl, step⟩

/-- Actual SW x16,4(x10), including the source-register read and all virtual
and physical checks. The selected mode is ordinary. -/
theorem store_plan [Platform] (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (base : rs .x10 = SpinlockImage.lockAddress)
    (enabled : rel.writeEnabled s 4 (writeRequest .counter false (storeWord rs)) (storeWord rs))
    (eligible : rel.writeModeEnabled s rr 4 (writeRequest .counter false (storeWord rs)) (storeWord rs) .ordinary) :
    Plan reads rel rs rr s (execute_STORE 4#12 (.Regidx 16#5) (.Regidx 10#5) 4)
      (fun result after rr' next => result = .Retire_Success () ∧
        writeFacts rel rs s .counter false (storeWord rs) after rr' next) := by
  have hwrite := vmem_write_plan reads rel rs rr s static off base .counter (storeWord rs) enabled eligible
  unfold execute_STORE
  apply prefix_plan reads rel (after := rs) (value := ())
  · exact Logic.EventWP.pure_plan reads rs _
  refine prefix_plan reads rel (rx16_plan reads rs) ?_
  apply prefix_plan reads rel (after := rs) (value := storeWord rs)
  · exact Logic.EventWP.pure_plan reads rs _
  refine Plan.bind hwrite ?_
  rintro _ after rr' next ⟨rfl, facts⟩
  exact .pure ⟨rfl, facts⟩

/-- Actual SW zero,0(x10). Architectural x0 is zero independently of the
unused x0 field in the generated register carrier. -/
theorem unlock_store_plan [Platform] (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : Static rs) (off : BootPmp.Off rs) (base : rs .x10 = SpinlockImage.lockAddress)
    (enabled : rel.writeEnabled s 4 (writeRequest .lock false 0#32) 0#32)
    (eligible : rel.writeModeEnabled s rr 4 (writeRequest .lock false 0#32) 0#32 .ordinary) :
    Plan reads rel rs rr s (execute_STORE 0#12 (.Regidx 0#5) (.Regidx 10#5) 4)
      (fun result after rr' next => result = .Retire_Success () ∧
        writeFacts rel rs s .lock false 0#32 after rr' next) := by
  have hwrite := vmem_write_plan reads rel rs rr s static off base .lock 0#32 enabled eligible
  unfold execute_STORE
  apply prefix_plan reads rel (after := rs) (value := ())
  · exact Logic.EventWP.pure_plan reads rs _
  apply prefix_plan reads rel (after := rs) (value := 0#32)
  · exact Logic.EventWP.pure_plan reads rs _
  refine Plan.bind hwrite ?_
  rintro _ after rr' next ⟨rfl, facts⟩
  exact .pure ⟨rfl, facts⟩

end MachCSL.Machine.SpinlockAccess
