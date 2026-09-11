import MachCSL.Machine.SpinlockWitnessHeldDefs

namespace MachCSL.Machine.SpinlockWitnessHeld
open MachCSL.Memory MachCSL.Machine.SpinlockWitness
open _root_.Sail.ConcurrencyInterfaceV1.Free
attribute [local instance] SpinlockWitness.platform

theorem writeFour_program (program : SailM Unit) (req : WriteRequest 4)
    (k : WriteResult → SailM Unit) (h : writeFour program = some (req, k)) :
    program = .impure (.writeMem 4 req) k := by
  unfold writeFour at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  · contradiction

theorem writer_eq (program : SailM Unit) (req : WriteRequest 4)
    (h : (writeFour program).map Prod.fst = some req) :
    writeFour program = some (writer program) ∧ (writer program).1 = req := by
  cases found : writeFour program with
  | none => simp [found] at h
  | some pair =>
    have same : pair.1 = req := by simpa only [found, Option.map_some, Option.some.injEq] using h
    exact ⟨by simp only [writer, found, Option.getD_some], by simpa only [writer, found, Option.getD_some] using same⟩

theorem writer_program (program : SailM Unit) (req : WriteRequest 4)
    (h : (writeFour program).map Prod.fst = some req) :
    program = .impure (.writeMem 4 req) (writer program).2 := by
  obtain ⟨found, same⟩ := writer_eq program req h
  exact (writeFour_program program (writer program).1 (writer program).2 found).trans
    (congrArg (fun q : WriteRequest 4 => (.impure (.writeMem 4 q) (writer program).2 : SailM Unit)) same)

theorem barrier_program (program : SailM Unit) (kind : _root_.barrier_kind)
    (h : (barrierNext program).map Prod.fst = some kind) :
    program = .impure (.barrier kind) (barrier program).2 := by
  unfold barrierNext at h
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst kind
    rfl
  · simp at h

def writeLocal (s : LocalState Device) (hart : Agent) (req : WriteRequest n)
    (word : BitVec (8 * n)) : LocalState Device :=
  { s with memory := writeBytes s.memory req.pa n word
           log := s.log ++ [⟨snapshot req.pa n word, hart⟩]
           view := if accessExclusive req.access_kind then s.log.length + 1 else s.view
           reservation := none }

theorem write_node (bus : Bus Device) (others : PhysicalAddress → Prop) (hart : Agent)
    (image : ByteMap 64) (s : LocalState Device) (req : WriteRequest n)
    (word : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (present : req.value = some word) (ram : deviceAddress req.pa = false)
    (free : Disjoint (Footprint req.pa n) others) :
    NodeStep bus others hart image s (.impure (.writeMem n req) k) (k (.Ok none))
      (writeLocal s hart req word) := by
  simp only [NodeStep, present, ram, Bool.false_eq_true, ↓reduceIte]
  exact Or.inr ⟨free, trivial, rfl⟩

theorem read_exclusive_node (bus : Bus Device) (others : PhysicalAddress → Prop) (hart : Agent)
    (image : ByteMap 64) (s : LocalState Device) (req : Logic.MemoryReadWP.ReadRequest n)
    (word : BitVec (8 * n)) (k : Logic.MemoryReadWP.ReadResult n → SailM Unit)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true)
    (free : Disjoint (Footprint req.pa n) others)
    (readable : readBytes s.memory req.pa n = some word) :
    NodeStep bus others hart image s (.impure (.readMem n req) k) (k (.Ok (word, none)))
      { s with view := s.log.length, reservation := some (snapshot req.pa n word) } := by
  simp only [NodeStep, ram, Bool.false_eq_true, ↓reduceIte]
  exact Or.inr ⟨exclusive, Or.inr ⟨free, word, readBytes_spec _ _ _ _ readable, rfl, rfl⟩⟩

theorem blocked_write_node (bus : Bus Device) (others : PhysicalAddress → Prop) (hart : Agent)
    (image : ByteMap 64) (s : LocalState Device) (req : WriteRequest n)
    (word : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (present : req.value = some word) (ram : deviceAddress req.pa = false)
    (blocked : ¬ Disjoint (Footprint req.pa n) others) :
    NodeStep bus others hart image s (.impure (.writeMem n req) k)
      (.impure (.writeMem n req) k) s := by
  simp only [NodeStep, present, ram, Bool.false_eq_true, ↓reduceIte]
  exact Or.inl ⟨blocked, trivial, trivial⟩

theorem barrier_node (bus : Bus Device) (others : PhysicalAddress → Prop) (hart : Agent)
    (image : ByteMap 64) (s : LocalState Device) (kind : _root_.barrier_kind)
    (k : Unit → SailM Unit) :
    NodeStep bus others hart image s (.impure (.barrier kind) k) (k ())
      { s with view := fencePost hart s.log (fenceDrains kind) s.view } := ⟨rfl, rfl⟩

end MachCSL.Machine.SpinlockWitnessHeld
