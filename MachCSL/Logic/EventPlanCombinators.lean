import MachCSL.Logic.EventPlanDefs
import MachCSL.Machine.BootPmpProgram

namespace MachCSL.Logic.EventPlan
open MachCSL.Memory MachCSL.Machine

variable {S α β : Type} {reads : EventWP.ReadAllowed} {rel : Relations S}

/-- Sequential composition preserves the actual residual free tree and every
register, reservation and protocol index. -/
theorem Plan.bind {rs rr s program} {next : α → SailM β}
    {P : α → RegisterFile → Option Reservation → S → Prop}
    {Q : β → RegisterFile → Option Reservation → S → Prop}
    (first : Plan reads rel rs rr s program P)
    (rest : ∀ value after rr' s', P value after rr' s' → Plan reads rel after rr' s' (next value) Q) :
    Plan reads rel rs rr s (program >>= next) Q := by
  induction first with
  | pure good => exact rest _ _ _ _ good
  | «prefix» first _ ih =>
    rw [BootPmp.sail_bind_assoc]
    exact .prefix first (fun value after good => ih value after good rest)
  | plain enabled ram kind _ ih =>
    exact .plain enabled ram kind (fun word s' step => ih word s' step rest)
  | exclusive enabled ram kind _ ih =>
    exact .exclusive enabled ram kind (fun word s' step => ih word s' step rest)
  | write enabled present ram mode eligible _ ih =>
    exact .write enabled present ram mode eligible (fun s' step => ih s' step rest)
  | barrier enabled _ ih =>
    exact .barrier enabled (fun s' step => ih s' step rest)

theorem Plan.mono {rs rr s program}
    {P Q : α → RegisterFile → Option Reservation → S → Prop}
    (plan : Plan reads rel rs rr s program P)
    (imp : ∀ value after rr' s', P value after rr' s' → Q value after rr' s') :
    Plan reads rel rs rr s program Q := by
  induction plan with
  | pure good => exact .pure (imp _ _ _ _ good)
  | «prefix» first _ ih => exact .prefix first (fun value after good => ih value after good imp)
  | plain enabled ram kind _ ih => exact .plain enabled ram kind (fun word s' step => ih word s' step imp)
  | exclusive enabled ram kind _ ih => exact .exclusive enabled ram kind (fun word s' step => ih word s' step imp)
  | write enabled present ram mode eligible _ ih => exact .write enabled present ram mode eligible (fun s' step => ih s' step imp)
  | barrier enabled _ ih => exact .barrier enabled (fun s' step => ih s' step imp)

abbrev Returns (reads : EventWP.ReadAllowed) (rel : Relations S)
    (rs : RegisterFile) (rr : Option Reservation) (s : S) (program : SailM α)
    (value : α) (after : RegisterFile) (rr' : Option Reservation) (s' : S) : Prop :=
  Plan reads rel rs rr s program (fun result file reservation state =>
    result = value ∧ file = after ∧ reservation = rr' ∧ state = s')

theorem pure_plan (reads : EventWP.ReadAllowed) (rel : Relations S)
    (rs : RegisterFile) (rr : Option Reservation) (s : S) (value : α) :
    Returns reads rel rs rr s (.pure value) value rs rr s := .pure ⟨rfl, rfl, rfl, rfl⟩

theorem Returns.bind {rs rr s middle rm sm after ra sa} {program : SailM α}
    {next : α → SailM β} {value result}
    (first : Returns reads rel rs rr s program value middle rm sm)
    (rest : Returns reads rel middle rm sm (next value) result after ra sa) :
    Returns reads rel rs rr s (program >>= next) result after ra sa :=
  Plan.bind first fun _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩ => rest

theorem Returns.liftExcept {rs rr s after ra sa} {program : SailM α} {value : α}
    (plan : Returns reads rel rs rr s program value after ra sa) (ε : Type) :
    Returns reads rel rs rr s (monadLift program : SailME ε α).run (.ok value) after ra sa := by
  change Returns reads rel rs rr s (program >>= fun a => Sail.ArchSem.FreeM.pure (Except.ok a)) (.ok value) after ra sa
  exact plan.bind (pure_plan reads rel after ra sa _)

theorem Returns.exceptBind {ε : Type} {rs rr s middle rm sm after ra sa}
    {program : SailME ε α} {next : α → SailME ε β} {a : α} {b : β}
    (first : Returns reads rel rs rr s program.run (.ok a) middle rm sm)
    (second : Returns reads rel middle rm sm (next a).run (.ok b) after ra sa) :
    Returns reads rel rs rr s (program >>= next).run (.ok b) after ra sa :=
  first.bind second

theorem sail_bind_pure_eq (program : SailM α) : (program >>= pure) = program := by
  induction program with
  | pure value => rfl
  | impure event next ih =>
    apply congrArg (Sail.ArchSem.FreeM.impure event)
    funext value
    exact ih value

/-- Embedding an existing prefix leaves reservation and protocol state unchanged. -/
theorem of_execPlan {rs rr s program} {P : α → RegisterFile → Prop}
    (plan : EventWP.ExecPlan reads rs program P) :
    Plan reads rel rs rr s program (fun value after rr' s' =>
      P value after ∧ rr' = rr ∧ s' = s) := by
  have bound : Plan reads rel rs rr s (program >>= pure)
      (fun value after rr' s' => P value after ∧ rr' = rr ∧ s' = s) :=
    Plan.prefix plan (fun value after good =>
    (Plan.pure (reads := reads) (rel := rel) (rr := rr) (s := s)
      (value := value) ⟨good, rfl, rfl⟩))
  simpa only [sail_bind_pure_eq] using bound

theorem of_returns {rs rr s after program} {value : α}
    (plan : EventWP.Returns reads rs program value after) :
    Returns reads rel rs rr s program value after rr s :=
  (of_execPlan plan).mono fun _ _ _ _ ⟨⟨hv, hf⟩, hr, hs⟩ => ⟨hv, hf, hr, hs⟩

/-- Branch-preserving transformer lift; no concrete returned word is selected. -/
theorem Plan.liftExcept {rs rr s program} {P : α → RegisterFile → Option Reservation → S → Prop}
    (plan : Plan reads rel rs rr s program P) (ε : Type) :
    Plan reads rel rs rr s (monadLift program : SailME ε α).run
      (fun result after rr' s' => ∃ value, result = .ok value ∧ P value after rr' s') := by
  change Plan reads rel rs rr s (program >>= fun a => Sail.ArchSem.FreeM.pure (Except.ok a)) _
  exact plan.bind fun value after rr' s' good => .pure ⟨value, rfl, good⟩

/-- Every proved successful result gets its own actual ExceptT continuation. -/
theorem Plan.exceptBind {ε : Type} {rs rr s} {program : SailME ε α} {next : α → SailME ε β}
    {P : α → RegisterFile → Option Reservation → S → Prop}
    {Q : Except ε β → RegisterFile → Option Reservation → S → Prop}
    (first : Plan reads rel rs rr s program.run
      (fun result after rr' s' => ∃ value, result = .ok value ∧ P value after rr' s'))
    (rest : ∀ value after rr' s', P value after rr' s' →
      Plan reads rel after rr' s' (next value).run Q) :
    Plan reads rel rs rr s (program >>= next).run Q :=
  first.bind fun _ after rr' s' ⟨value, eq, good⟩ => by
    subst eq
    exact rest value after rr' s' good

end MachCSL.Logic.EventPlan
