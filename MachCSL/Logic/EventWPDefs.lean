import MachCSL.Logic.RegisterWPDefs
import MachCSL.Logic.MemoryReadWPDefs

/-! Event-by-event proof plans. Hardware pin reads branch universally and
independently; the symbolic register table describes only owned CPU registers. -/
namespace MachCSL.Logic.EventWP
open Iris Iris.Std Iris.BI MachCSL.Machine
open _root_.Sail.ConcurrencyInterfaceV1.Free

def IsPin (r : Register) : Prop := r = .sig_seip ∨ r = .sig_meip

def IsOwned (r : Register) : Prop := ¬ IsPin r

instance (r : Register) : Decidable (IsPin r) := inferInstanceAs (Decidable (_ ∨ _))
instance (r : Register) : Decidable (IsOwned r) := inferInstanceAs (Decidable (¬ IsPin r))

/-- Exact native register map with only the two asynchronously written pin keys removed. -/
def ownedMap (rs : RegisterFile) : Registers.RegisterMap Registers.Value :=
  PartialMap.delete (PartialMap.delete (Registers.initialMap rs) .sig_seip) .sig_meip

def ownedCells {GF : BundledGFunctors} (capacity : Registers.Capacity GF)
    (γ : GName) (rs : RegisterFile) : IProp GF :=
  letI := capacity.registers
  iprop([∗map] r ↦ value ∈ ownedMap rs, ghost_map_elem γ (.own 1) r value)

/-- Pure interface needed for map rearrangement. Linking discharges this with the
existing checked initialMap theorem, independently of the WP rule interfaces. -/
structure InitialMapFacts : Prop where
  lookup : ∀ (rs : RegisterFile) (r : Register),
    PartialMap.get? (Registers.initialMap rs) r = some (⟨r, rs r⟩ : Registers.Value)

abbrev ReadAllowed := (n : Nat) → MemoryReadWP.ReadRequest n → BitVec (8 * n) → Prop

/-- A finite proof plan covers every result of each unowned pin read. It is not
an existential execution trace and does not assert that a whole instruction is atomic.
`ReadAllowed` is discharged through actual byte/pristine ownership by the WP fold. -/
inductive ExecPlan (reads : ReadAllowed) :
    (rs : RegisterFile) → SailM α → (α → RegisterFile → Prop) → Prop where
  | pure {rs value Q} (post : Q value rs) : ExecPlan reads rs (.pure value) Q
  | readOwned {rs r k Q} (owned : IsOwned r)
      (rest : ExecPlan reads rs (k (rs r)) Q) :
      ExecPlan reads rs (.impure (.readReg r) k) Q
  | readPin {rs r k Q} (pin : IsPin r)
      (rest : ∀ value : RegisterType r, ExecPlan reads rs (k value) Q) :
      ExecPlan reads rs (.impure (.readReg r) k) Q
  | writeOwned {rs r value k Q} (owned : IsOwned r)
      (rest : ExecPlan reads (Sail.Registers.write rs r value) (k ()) Q) :
      ExecPlan reads rs (.impure (.writeReg r value) k) Q
  | readMem {rs n req word k Q} (ram : deviceAddress req.pa = false)
      (plain : accessExclusive req.access_kind = false) (allowed : reads n req word)
      (rest : ExecPlan reads rs (k (.Ok (word, none))) Q) :
      ExecPlan reads rs (.impure (.readMem n req) k) Q

theorem ExecPlan.bind {reads : ReadAllowed} {rs : RegisterFile} {program : SailM α}
    {next : α → SailM β} {P : α → RegisterFile → Prop} {Q : β → RegisterFile → Prop}
    (first : ExecPlan reads rs program P)
    (rest : ∀ value after, P value after → ExecPlan reads after (next value) Q) :
    ExecPlan reads rs (program >>= next) Q := by
  induction first with
  | pure post => exact rest _ _ post
  | readOwned owned _ ih => exact .readOwned owned (ih rest)
  | readPin pin _ ih => exact .readPin pin (fun value => ih value rest)
  | writeOwned owned _ ih => exact .writeOwned owned (ih rest)
  | readMem ram plain allowed _ ih => exact .readMem ram plain allowed (ih rest)

theorem ExecPlan.mono {reads : ReadAllowed} {rs : RegisterFile} {program : SailM α}
    {P Q : α → RegisterFile → Prop} (plan : ExecPlan reads rs program P)
    (imp : ∀ value after, P value after → Q value after) : ExecPlan reads rs program Q := by
  induction plan with
  | pure post => exact .pure (imp _ _ post)
  | readOwned owned _ ih => exact .readOwned owned (ih imp)
  | readPin pin _ ih => exact .readPin pin (fun value => ih value imp)
  | writeOwned owned _ ih => exact .writeOwned owned (ih imp)
  | readMem ram plain allowed _ ih => exact .readMem ram plain allowed (ih imp)

abbrev Returns (reads : ReadAllowed) (rs : RegisterFile) (program : SailM α)
    (value : α) (after : RegisterFile) : Prop :=
  ExecPlan reads rs program (fun result file => result = value ∧ file = after)

theorem Returns.bind {reads : ReadAllowed} {rs middle after : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : Returns reads rs program value middle)
    (rest : Returns reads middle (next value) result after) :
    Returns reads rs (program >>= next) result after :=
  ExecPlan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

theorem pure_plan (reads : ReadAllowed) (rs : RegisterFile) (value : α) :
    Returns reads rs (.pure value) value rs := .pure ⟨rfl, rfl⟩

theorem read_plan (reads : ReadAllowed) (rs : RegisterFile) (r : Register) (owned : IsOwned r) :
    Returns reads rs (PreSail.readReg r) (rs r) rs := .readOwned owned (.pure ⟨rfl, rfl⟩)

theorem write_plan (reads : ReadAllowed) (rs : RegisterFile) (r : Register)
    (value : RegisterType r) (owned : IsOwned r) :
    Returns reads rs (PreSail.writeReg r value) () (Sail.Registers.write rs r value) :=
  .writeOwned owned (.pure ⟨rfl, rfl⟩)

/-- Resource-only RAM interface: extraction and restoration of actual byte and
pristine timestamp windows. No callee WP or semantic successor is assumed here. -/
structure RamAccess {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (reads : ReadAllowed) (dq : DFrac) (resources : IProp GF) : Prop where
  access : ∀ n req word, reads n req word →
    iprop(⊢ resources -∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word ∗
      TsoRead.pristineWindow capacity.era.heap.ledger era.timestamps req.pa n ∗
      (TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
        TsoRead.pristineWindow capacity.era.heap.ledger era.timestamps req.pa n -∗ resources))

end MachCSL.Logic.EventWP
