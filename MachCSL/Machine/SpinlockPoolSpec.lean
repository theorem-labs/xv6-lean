import MachCSL.Machine.SpinlockPoolUpdateDefs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.SpinlockProtocol Logic.EventPlan

/-- Exact cursor boundary records. Actual machine transitions are supplied by
AStep separately; no constructor assumes PoolInv preservation. -/
inductive CursorEdge [Platform] (cpu : CPU) : Cursor → SailM Unit → Cursor → SailM Unit → Prop where
  | restart (c : Cursor) (i : Fin 17) (tick : Bool)
      (family : SpinlockFamily.Family cpu i c.registers c.phase) :
      CursorEdge cpu c (.pure ()) { c with fetch := i, reservation := none } (cycle tick)
  | readOwned (c : Cursor) (r : Register) (k : RegisterType r → SailM Unit)
      (owned : EventWP.IsOwned r) :
      CursorEdge cpu c (.impure (.readReg r) k) c (k (c.registers r))
  | readPin (c : Cursor) (r : Register) (k : RegisterType r → SailM Unit)
      (pin : EventWP.IsPin r) (value : RegisterType r) :
      CursorEdge cpu c (.impure (.readReg r) k) c (k value)
  | writeOwned (c : Cursor) (r : Register) (value : RegisterType r) (k : Unit → SailM Unit)
      (owned : EventWP.IsOwned r) :
      CursorEdge cpu c (.impure (.writeReg r value) k)
        { c with registers := Sail.Registers.write c.registers r value } (k ())
  | codeRead (c : Cursor) (n : Nat) (req : ReadRequest n) (word : BitVec (8 * n))
      (k : MemoryReadWP.ReadResult n → SailM Unit)
      (allowed : SpinlockFetch.CodeRead c.fetch n req word)
      (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
      CursorEdge cpu c (.impure (.readMem n req) k) c (k (.Ok (word, none)))
  | plain (c : Cursor) (n : Nat) (req : ReadRequest n) (word : BitVec (8 * n))
      (next : Phase) (k : MemoryReadWP.ReadResult n → SailM Unit)
      (step : relations.plain c.phase n req word next)
      (ram : deviceAddress req.pa = false) (kind : accessExclusive req.access_kind = false) :
      CursorEdge cpu c (.impure (.readMem n req) k) { c with phase := next } (k (.Ok (word, none)))
  | exclusive (c : Cursor) (n : Nat) (req : ReadRequest n) (word : BitVec (8 * n))
      (next : Phase) (k : MemoryReadWP.ReadResult n → SailM Unit)
      (step : relations.exclusive c.phase n req word next)
      (ram : deviceAddress req.pa = false) (kind : accessExclusive req.access_kind = true) :
      CursorEdge cpu c (.impure (.readMem n req) k)
        { c with phase := next, reservation := some (snapshot req.pa n word) } (k (.Ok (word, none)))
  | exclusiveBlocked (c : Cursor) (n : Nat) (req : ReadRequest n)
      (k : MemoryReadWP.ReadResult n → SailM Unit)
      (enabled : relations.exclusiveEnabled c.phase n req)
      (ram : deviceAddress req.pa = false) (kind : accessExclusive req.access_kind = true) :
      CursorEdge cpu c (.impure (.readMem n req) k)
        { c with reservation := none } (.impure (.readMem n req) k)
  | write (c : Cursor) (n : Nat) (req : WriteRequest n) (word : BitVec (8 * n))
      (next : Phase) (k : MemoryWriteWP.WriteResult → SailM Unit)
      (present : req.value = some word) (ram : deviceAddress req.pa = false)
      (mode : WriteMode n req c.reservation)
      (eligible : relations.writeModeEnabled c.phase c.reservation n req word mode)
      (step : relations.write c.phase n req word next) :
      CursorEdge cpu c (.impure (.writeMem n req) k)
        { c with phase := next, reservation := none } (k (.Ok none))
  | writeBlocked (c : Cursor) (n : Nat) (req : WriteRequest n) (word : BitVec (8 * n))
      (k : MemoryWriteWP.WriteResult → SailM Unit)
      (present : req.value = some word) (ram : deviceAddress req.pa = false)
      (mode : WriteMode n req c.reservation)
      (eligible : relations.writeModeEnabled c.phase c.reservation n req word mode) :
      CursorEdge cpu c (.impure (.writeMem n req) k) c (.impure (.writeMem n req) k)
  | barrier (c : Cursor) (kind : barrier_kind) (next : Phase) (k : Unit → SailM Unit)
      (step : relations.barrier c.phase kind next) :
      CursorEdge cpu c (.impure (.barrier kind) k) { c with phase := next } (k ())

/-- The actual event result and cursor change are recorded by CursorEdge.
Source Step still determines all physical updates, observations and guards. -/
inductive Transition [Platform] : AnnotatedPool.Transition Label where
  | hart {gen cpu program program' cursor cursor' g g'}
      (live : ThreadLive g gen) (edge : CursorEdge cpu cursor program cursor' program')
      (update : nextCursor g g' cpu program cursor = some cursor') :
      Transition (.hart gen cpu program, .hart cursor) g [] (.hart gen cpu program', .hart cursor') g' []
  | stale {gen cpu program cursor g} (dead : ¬ ThreadLive g gen) :
      Transition (.hart gen cpu program, .hart cursor) g [] (.hart gen cpu program, .hart cursor) g []
  | uart {gen g g' observations} :
      Transition (.uart gen, .worker) g observations (.uart gen, .worker) g' []
  | disk {gen g g'} : Transition (.disk gen, .worker) g [] (.disk gen, .worker) g' []
  | plic {gen g g'} : Transition (.plic gen, .worker) g [] (.plic gen, .worker) g' []
  | powerOff {g g'} (on : g.power = true) :
      Transition (.power, .worker) g [.powerOff] (.power, .worker) g' []
  | powerOn {g g'} (off : g.power = false) :
      Transition (.power, .worker) g [.powerOn] (.power, .worker) g' (freshForks g')

/-- Final application obligations, inhabited by SpinlockPoolCoverProofs.actual.
Covers is proved from actual cases, never supplied by a closed client. -/
structure SpinlockPoolSpec [Platform] : Prop where
  initial : ∀ initial : State, initial.power = false → initial.generation = 0 →
    PoolInv ([(.power, .worker)], initial)
  covers : AnnotatedPool.Covers SpinlockImage.image Transition PoolInv
  exclusion : ∀ config cpu other, PoolInv config → Holds config cpu → Holds config other → cpu = other

end MachCSL.Machine.SpinlockPool
