import MachCSL.Logic.EventPlanHeadDefs

namespace MachCSL.Logic.EventPlanHead
open MachCSL.Memory MachCSL.Machine EventPlan
variable {S α β : Type} {reads : EventWP.ReadAllowed} {rel : Relations S}

/-- Decompose the real ExecPlan prefix. Its remaining free tree stays inside
an ordinary prefix Plan; only a pure prefix proceeds directly to the supplied
continuation's head. -/
theorem prefix_head {rs rr s} {program : SailM α} {next : α → SailM β}
    {P : α → RegisterFile → Prop} {Q : β → RegisterFile → Option Reservation → S → Prop}
    (first : EventWP.ExecPlan reads rs program P)
    (rest : ∀ value after, P value after → Plan reads rel after rr s (next value) Q)
    (heads : ∀ value after, P value after → Head reads rel after rr s (next value) Q) :
    Head reads rel rs rr s (program >>= next) Q := by
  cases first with
  | pure good => exact heads _ _ good
  | readOwned owned tail => exact .readOwned owned (.prefix tail rest)
  | readPin pin tail => exact .readPin pin (fun value => .prefix (tail value) rest)
  | writeOwned owned tail => exact .writeOwned owned (.prefix tail rest)
  | readMem ram plain allowed tail => exact .codeRead ram plain allowed (.prefix tail rest)

/-- Every existing plan exposes exactly one actual free-tree head, even when
its proof used arbitrarily nested prefix/continuation compositions. -/
theorem head_of_plan {rs rr s} {program : SailM α}
    {Q : α → RegisterFile → Option Reservation → S → Prop}
    (plan : Plan reads rel rs rr s program Q) : Head reads rel rs rr s program Q := by
  induction plan with
  | pure good => exact .pure good
  | «prefix» first rest ih => exact prefix_head first rest ih
  | plain enabled ram kind rest _ => exact .plain enabled ram kind rest
  | exclusive enabled ram kind rest _ => exact .exclusive enabled ram kind rest
  | write enabled present ram mode eligible rest _ => exact .write enabled present ram mode eligible rest
  | barrier enabled rest _ => exact .barrier enabled rest

/-- Reconstruct the existing Plan without changing any event or postcondition. -/
theorem plan_of_head {rs rr s} {program : SailM α}
    {Q : α → RegisterFile → Option Reservation → S → Prop}
    (head : Head reads rel rs rr s program Q) : Plan reads rel rs rr s program Q := by
  cases head with
  | pure good => exact .pure good
  | @readOwned r k Q owned rest =>
    refine Plan.prefix (next := k) (EventWP.read_plan reads rs r owned) ?_
    intro result after good
    rcases good with ⟨hv, ha⟩
    subst result
    subst after
    exact rest
  | @readPin r k Q pin rest =>
    have first : EventWP.ExecPlan reads rs
        (.impure (.readReg r) (fun value => .pure value)) (fun _ after => after = rs) :=
      .readPin pin (fun _ => .pure rfl)
    refine Plan.prefix (next := k) first ?_
    intro value after good
    subst after
    exact rest value
  | @writeOwned r value k Q owned rest =>
    refine Plan.prefix (next := k) (EventWP.write_plan reads rs r value owned) ?_
    intro result after good
    rcases good with ⟨hv, ha⟩
    subst result
    subst after
    exact rest
  | @codeRead n req word k Q ram plain allowed rest =>
    have first : EventWP.ExecPlan reads rs
        (.impure (.readMem n req) (fun result => .pure result))
        (fun result after => result = .Ok (word, none) ∧ after = rs) :=
      .readMem ram plain allowed (.pure ⟨rfl, rfl⟩)
    refine Plan.prefix (next := k) first ?_
    intro result after good
    rcases good with ⟨hv, ha⟩
    subst result
    subst after
    exact rest
  | plain enabled ram kind rest => exact .plain enabled ram kind rest
  | exclusive enabled ram kind rest => exact .exclusive enabled ram kind rest
  | write enabled present ram mode eligible rest => exact .write enabled present ram mode eligible rest
  | barrier enabled rest => exact .barrier enabled rest

theorem plan_iff_head {rs rr s} {program : SailM α}
    {Q : α → RegisterFile → Option Reservation → S → Prop} :
    Plan reads rel rs rr s program Q ↔ Head reads rel rs rr s program Q :=
  ⟨head_of_plan, plan_of_head⟩

theorem pure_iff {rs rr s value} {Q : α → RegisterFile → Option Reservation → S → Prop} :
    Plan reads rel rs rr s (.pure value) Q ↔ Q value rs rr s := by
  constructor
  · intro plan
    cases head_of_plan plan with
    | pure good => exact good
  · exact Plan.pure

theorem read_register_cases {rs rr s r} {k : RegisterType r → SailM α}
    {Q : α → RegisterFile → Option Reservation → S → Prop}
    (plan : Plan reads rel rs rr s (.impure (.readReg r) k) Q) :
    (EventWP.IsOwned r ∧ Plan reads rel rs rr s (k (rs r)) Q) ∨
    (EventWP.IsPin r ∧ ∀ value, Plan reads rel rs rr s (k value) Q) := by
  cases head_of_plan plan with
  | readOwned owned rest => exact .inl ⟨owned, rest⟩
  | readPin pin rest => exact .inr ⟨pin, rest⟩

theorem write_register_cases {rs rr s r value} {k : Unit → SailM α}
    {Q : α → RegisterFile → Option Reservation → S → Prop}
    (plan : Plan reads rel rs rr s (.impure (.writeReg r value) k) Q) :
    EventWP.IsOwned r ∧ Plan reads rel (Sail.Registers.write rs r value) rr s (k ()) Q := by
  cases head_of_plan plan with
  | writeOwned owned rest => exact ⟨owned, rest⟩

theorem read_memory_cases {rs rr s n} {req : ReadRequest n}
    {k : MemoryReadWP.ReadResult n → SailM α}
    {Q : α → RegisterFile → Option Reservation → S → Prop}
    (plan : Plan reads rel rs rr s (.impure (.readMem n req) k) Q) :
    (∃ word, deviceAddress req.pa = false ∧ accessExclusive req.access_kind = false ∧
      reads n req word ∧ Plan reads rel rs rr s (k (.Ok (word, none))) Q) ∨
    (rel.plainEnabled s n req ∧ deviceAddress req.pa = false ∧ accessExclusive req.access_kind = false ∧
      ∀ word next, rel.plain s n req word next → Plan reads rel rs rr next (k (.Ok (word, none))) Q) ∨
    (rel.exclusiveEnabled s n req ∧ deviceAddress req.pa = false ∧ accessExclusive req.access_kind = true ∧
      ∀ word next, rel.exclusive s n req word next →
        Plan reads rel rs (some (snapshot req.pa n word)) next (k (.Ok (word, none))) Q) := by
  cases head_of_plan plan with
  | codeRead ram plain allowed rest => exact .inl ⟨_, ram, plain, allowed, rest⟩
  | plain enabled ram kind rest => exact .inr (.inl ⟨enabled, ram, kind, rest⟩)
  | exclusive enabled ram kind rest => exact .inr (.inr ⟨enabled, ram, kind, rest⟩)

theorem write_memory_cases {rs rr s n} {req : WriteRequest n}
    {k : MemoryWriteWP.WriteResult → SailM α}
    {Q : α → RegisterFile → Option Reservation → S → Prop}
    (plan : Plan reads rel rs rr s (.impure (.writeMem n req) k) Q) :
    ∃ value, rel.writeEnabled s n req value ∧ req.value = some value ∧ deviceAddress req.pa = false ∧
      ∃ mode : WriteMode n req rr, rel.writeModeEnabled s rr n req value mode ∧
        ∀ next, rel.write s n req value next → Plan reads rel rs none next (k (.Ok none)) Q := by
  cases head_of_plan plan with
  | write enabled present ram mode eligible rest => exact ⟨_, enabled, present, ram, mode, eligible, rest⟩

theorem barrier_cases {rs rr s kind} {k : Unit → SailM α}
    {Q : α → RegisterFile → Option Reservation → S → Prop}
    (plan : Plan reads rel rs rr s (.impure (.barrier kind) k) Q) :
    rel.barrierEnabled s kind ∧ ∀ next, rel.barrier s kind next → Plan reads rel rs rr next (k ()) Q := by
  cases head_of_plan plan with
  | barrier enabled rest => exact ⟨enabled, rest⟩

end MachCSL.Logic.EventPlanHead
