import MachCSL.Machine.AnnotatedPoolDefs
import MachCSL.Machine.SpinlockFamilyPlans
import MachCSL.Machine.SpinlockCodeIntegrityProofs
import MachCSL.Logic.EventPlanHeadProofs

/-! Concrete data and pure interpretation for the proposed operational
spinlock simulation. No preservation or all-run theorem is asserted here. -/
namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.SpinlockProtocol

structure Cursor where
  fetch : Fin 17
  registers : RegisterFile
  reservation : Option Reservation
  phase : Phase

inductive Label where
  | hart (cursor : Cursor)
  | worker

abbrev Pool := AnnotatedPool.Pool Label
abbrev Config := AnnotatedPool.Config Label

def OwnedMatch (physical symbolic : RegisterFile) : Prop :=
  ∀ r, EventWP.IsOwned r → physical r = symbolic r

def CursorControl (g : State) (cpu : CPU) (program : SailM Unit) (c : Cursor) : Prop :=
  OwnedMatch (g.registers cpu) c.registers ∧ c.reservation = g.reservations cpu ∧
  EventPlan.Plan (SpinlockFetch.CodeRead c.fetch) relations c.registers c.reservation c.phase program
    (fun _ after _ next => ∃ i, SpinlockFamily.Family cpu i after next)

def LatestWord (g : State) (address : PhysicalAddress) (word : BitVec 32) (time : Nat) : Prop :=
  ∀ j, j < 4 → Latest g.image g.log (addressAdd address j) time (nthByte word j)

/-- Pure history witnesses, not native Iris camera ownership. -/
structure Words where
  owner : Option (CPU × Nat)
  lockTime : Nat
  counter : BitVec 32
  counterTime : Nat

def Words.lockValue (w : Words) : BitVec 32 := if w.owner.isSome then 1#32 else 0#32

def WordsOK (g : State) (w : Words) : Prop :=
  LatestWord g SpinlockImage.lockAddress w.lockValue w.lockTime ∧
  LatestWord g SpinlockImage.counterAddress w.counter w.counterTime

def Winning (g : State) (cpu : CPU) (B : Nat) : Prop :=
  0 < B ∧ B ≤ g.views cpu ∧
  g.log[B - 1]? = some ⟨snapshot SpinlockImage.lockAddress 4 1#32, hartAgent cpu⟩

def HolderPosition : Phase → Option Nat
  | .held B _ _ | .loaded B _ _ | .stored B _ _ => some B
  | _ => none

def HeldFacts (g : State) (w : Words) (cpu : CPU) (B : Nat) (v : BitVec 32) (t : Nat) : Prop :=
  w.owner = some (cpu, B) ∧ w.counter = v ∧ w.counterTime = t ∧ Winning g cpu B

def PhaseOK (g : State) (w : Words) (cpu : CPU) (c : Cursor) : Prop :=
  match c.phase with
  | .idle => True
  | .reserved old => (old = 0#32 ∨ old = 1#32) ∧
      c.reservation = some (snapshot SpinlockImage.lockAddress 4 old)
  | .held B v t | .loaded B v t => HeldFacts g w cpu B v t ∧ t ≤ B
  | .stored B v t => HeldFacts g w cpu B v t

def generationOf : Expr → Option Nat
  | .hart gen _ _ | .uart gen | .disk gen | .plic gen => some gen
  | .power => none

def LabelMatches : Expr → Label → Prop
  | .hart _ _ _, .hart _ => True
  | .uart _, .worker | .disk _, .worker | .plic _, .worker | .power, .worker => True
  | _, _ => False

def currentHarts (pool : Pool) (generation : Nat) : List CPU :=
  pool.filterMap fun entry => match entry.1 with
    | .hart gen cpu _ => if gen = generation then some cpu else none
    | _ => none

structure Shape (pool : Pool) (g : State) : Prop where
  labels : ∀ e label, (e, label) ∈ pool → LabelMatches e label
  power : (pool.filter fun entry => match entry.1 with | .power => true | _ => false).length = 1
  generations : ∀ e label, (e, label) ∈ pool → ∀ gen, generationOf e = some gen →
    gen ≤ g.generation ∧ (g.power = false → gen < g.generation)
  current : g.power = true → (currentHarts pool g.generation).Perm (List.finRange 8)

def OwnerPresent (pool : Pool) (g : State) (w : Words) : Prop :=
  ∀ cpu B, w.owner = some (cpu, B) → ∃ program c,
    (Expr.hart g.generation cpu program, Label.hart c) ∈ pool ∧ HolderPosition c.phase = some B

def LiveCursors (pool : Pool) (g : State) (w : Words) : Prop :=
  ∀ gen cpu program c, (Expr.hart gen cpu program, Label.hart c) ∈ pool →
    ThreadLive g gen → CursorControl g cpu program c ∧ PhaseOK g w cpu c

def ResetVirtio (g : State) : Prop :=
  ∃ previous, g.devices.virtio = Devices.Virtio.virtio_reset previous

def PoolInv (config : Config) : Prop :=
  Shape config.1 config.2 ∧ (config.2.power = true →
    MemoryOK config.2 ∧ ReservationsOK config.2 ∧
    config.2.image = loadedRam SpinlockImage.image ∧ ResetVirtio config.2 ∧
    SpinlockCodeIntegrity.CodeUnwritten config.2.log ∧
    ∃ w, WordsOK config.2 w ∧ LiveCursors config.1 config.2 w ∧ OwnerPresent config.1 config.2 w)

/-- The whole post-commit/pre-unlock window, including interior continuations. -/
def Holds (config : Config) (cpu : CPU) : Prop :=
  config.2.power = true ∧ ∃ program c B,
    (Expr.hart config.2.generation cpu program, Label.hart c) ∈ config.1 ∧
    HolderPosition c.phase = some B

def initialCursor (g : State) (cpu : CPU) : Cursor :=
  ⟨⟨0, by decide⟩, g.registers cpu, g.reservations cpu, .idle⟩

def freshForks (g : State) : Pool :=
  (List.ofFn fun cpu : CPU => (loop g.generation cpu, Label.hart (initialCursor g cpu))) ++
    [(Expr.uart g.generation, .worker), (Expr.disk g.generation, .worker), (Expr.plic g.generation, .worker)]

end MachCSL.Machine.SpinlockPool
