import MachCSL.Sail.Model
import MachCSL.Sail.Registers
import MachCSL.Memory.Bytes

/-! Hart-local sub-instruction rules from `iris/RiscvLang.v:mnode_step`
at the pinned paper revision. The MMIO bus is an explicit data parameter here;
only its concrete device instantiation can define the intended system. These
rules do not yet prove cross-backend correspondence or machine adequacy. -/
namespace MachCSL.Machine

open Memory
open _root_.Sail.ConcurrencyInterfaceV1
open _root_.Sail.ConcurrencyInterfaceV1.Free
open LeanPaperStock.Functions

abbrev RegisterFile := Sail.Registers.File RegisterType
abbrev Reservation := ByteMap 64

structure Bus (Device : Type) where
  read : Device → PhysicalAddress → (n : Nat) → Option (BitVec (8 * n) × Device)
  write : Device → PhysicalAddress → (n : Nat) → BitVec (8 * n) → Option Device

def deviceAddress (address : PhysicalAddress) : Bool := address.toNat < 0x80000000

structure LocalState (Device : Type) where
  registers : RegisterFile
  memory : ByteMap 64
  devices : Device
  log : WriteLog 64
  view : Nat
  reservation : Option Reservation

def LocalState.setReg (s : LocalState Device) (r : Register) (v : RegisterType r) :
    LocalState Device := { s with registers := Sail.Registers.write s.registers r v }

def varietyExclusive : Access_variety → Bool
  | .AV_plain => false
  | .AV_exclusive | .AV_atomic_rmw => true

def accessExclusive : Access_kind RISCV_strong_access → Bool
  | .AK_explicit kind => varietyExclusive kind.variety
  | .AK_arch kind => varietyExclusive kind.variety
  | .AK_ifetch _ | .AK_ttw _ => false

def fenceDrains : barrier_kind → Bool
  | .Barrier_RISCV_rw_rw | .Barrier_RISCV_rw_r
  | .Barrier_RISCV_w_rw | .Barrier_RISCV_w_r => true
  | _ => false

/-- Source `riscv_step`: one real fetch/execute cycle and an optional clock tick. -/
def cycle [Platform] (tick : Bool) : SailM Unit := do
  let _ ← try_step 0 false
  if tick then tick_clock () else pure ()

def NodeStep [Platform] (bus : Bus Device) (others : PhysicalAddress → Prop)
    (hart : Agent) (image : ByteMap 64) (s : LocalState Device) (m : SailM Unit)
    (m' : SailM Unit) (s' : LocalState Device) : Prop :=
  match m with
  | .pure _ => ∃ tick, m' = cycle tick ∧ s' = { s with reservation := none }
  | .impure event k =>
    match event with
    | .readReg r => m' = k (s.registers r) ∧ s' = s
    | .writeReg r v => m' = k () ∧ s' = s.setReg r v
    | .readMem n req =>
      if deviceAddress req.pa then
        ∃ w d, bus.read s.devices req.pa n = some (w, d) ∧
          m' = k (.Ok (w, none)) ∧ s' = { s with devices := d }
      else
        (accessExclusive req.access_kind = false ∧
          ∃ view w, s.view ≤ view ∧ view ≤ s.log.length ∧
            ReadsBytes image s.log hart view req.pa n w ∧
            m' = k (.Ok (w, none)) ∧ s' = { s with view := view }) ∨
        (accessExclusive req.access_kind = true ∧
          ((¬ Disjoint (Footprint req.pa n) others ∧
            m' = m ∧ s' = { s with reservation := none }) ∨
           (Disjoint (Footprint req.pa n) others ∧
            ∃ w, (∀ j, j < n → s.memory (addressAdd req.pa j) = some (nthByte w j)) ∧
              m' = k (.Ok (w, none)) ∧
              s' = { s with
                view := s.log.length
                reservation := some (snapshot req.pa n w) })))
    | .writeMem n req =>
      match req.value with
      | none => False -- the builtin returns pure Ok None without emitting this event
      | some value =>
        if deviceAddress req.pa then
          ∃ d, bus.write s.devices req.pa n value = some d ∧
            m' = k (.Ok none) ∧ s' = { s with devices := d, reservation := none }
        else
          (¬ Disjoint (Footprint req.pa n) others ∧ m' = m ∧ s' = s) ∨
          (Disjoint (Footprint req.pa n) others ∧ m' = k (.Ok none) ∧
            s' = { s with
              memory := writeBytes s.memory req.pa n value
              log := s.log ++ [⟨snapshot req.pa n value, hart⟩]
              view := if accessExclusive req.access_kind then s.log.length + 1 else s.view
              reservation := none })
    | .barrier b => m' = k () ∧
        s' = { s with view := fencePost hart s.log (fenceDrains b) s.view }
    | .getCycleCount => m' = k (0 : Nat) ∧ s' = s
    | .choose _ => ∃ choice, m' = k choice ∧ s' = s
    | .instructionAnnounce _ _ | .branchAnnounce _ _ | .cacheOp _ | .tlbi _
    | .takeException _ | .returnException _ | .translationStart _ | .translationEnd _
    | .cycleCount | .print _ => m' = k () ∧ s' = s
    | .error _ | .discard => False

theorem read_register_step [Platform] (bus : Bus Device) (others) (hart) (image)
    (s : LocalState Device) (r : Register) (k : RegisterType r → SailM Unit) :
    NodeStep bus others hart image s (.impure (.readReg r) k) (k (s.registers r)) s :=
  ⟨rfl, rfl⟩

theorem write_register_step [Platform] (bus : Bus Device) (others) (hart) (image)
    (s : LocalState Device) (r : Register) (v : RegisterType r) (k : Unit → SailM Unit) :
    NodeStep bus others hart image s (.impure (.writeReg r v) k) (k ()) (s.setReg r v) :=
  ⟨rfl, rfl⟩

theorem restart_step [Platform] (bus : Bus Device) (others) (hart) (image)
    (s : LocalState Device) (tick : Bool) :
    NodeStep bus others hart image s (.pure ()) (cycle tick)
      { s with reservation := none } := ⟨tick, rfl, rfl⟩

theorem error_stuck [Platform] (bus : Bus Device) (others) (hart) (image)
    (s s' : LocalState Device) (error : _root_.Sail.Error exception)
    (k : Empty → SailM Unit) (m') :
    ¬ NodeStep bus others hart image s (.impure (.error error) k) m' s' := id

theorem discard_stuck [Platform] (bus : Bus Device) (others) (hart) (image)
    (s s' : LocalState Device) (k : Empty → SailM Unit) (m') :
    ¬ NodeStep bus others hart image s (.impure .discard k) m' s' := id

end MachCSL.Machine
