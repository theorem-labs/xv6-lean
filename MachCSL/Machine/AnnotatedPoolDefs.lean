import MachCSL.Machine.Reachability

/-! Proof annotations on the actual pool. Erasure retains every real expression,
state, observation and fork; annotations do not define another interpreter. -/
namespace MachCSL.Machine.AnnotatedPool

abbrev Pool (Label : Type) := List (Expr × Label)
abbrev Config (Label : Type) := Pool Label × State

def erase (pool : Pool Label) : List Expr := pool.map Prod.fst
def eraseConfig (config : Config Label) : Configuration := (erase config.1, config.2)

/-- The application relates one real primitive event to its bookkeeping.
It must account for blocked events, stale threads, devices and power forks. -/
abbrev Transition (Label : Type) :=
  (Expr × Label) → State → List Observation → (Expr × Label) → State → Pool Label → Prop

inductive AStep [Platform] (image : BootImage) (transition : Transition Label) :
    Config Label → List Observation → Config Label → Prop where
  | atomic {e label g observations e' label' g' forks}
      (actual : Step image e g observations e' g' (erase forks))
      (annotation : transition (e, label) g observations (e', label') g' forks)
      (left right : Pool Label) :
      AStep image transition (left ++ (e, label) :: right, g) observations
        (left ++ (e', label') :: right ++ forks, g')

inductive ASteps [Platform] (image : BootImage) (transition : Transition Label) :
    Nat → Config Label → List Observation → Config Label → Prop where
  | refl (config) : ASteps image transition 0 config [] config
  | cons {n before middle after observations rest}
      (first : AStep image transition before observations middle)
      (next : ASteps image transition n middle rest after) :
      ASteps image transition (n + 1) before (observations ++ rest) after

/-- Explicit application obligation, not an assumed global instance. Every
actual event must admit annotations and preserve the concrete pool invariant.
Final application theorems must construct this contract from their protocol. -/
def Covers [Platform] (image : BootImage) (transition : Transition Label)
    (invariant : Config Label → Prop) : Prop :=
  ∀ left right e label g observations e' g' forks,
    invariant (left ++ (e, label) :: right, g) →
    Step image e g observations e' g' forks →
    ∃ label' annotatedForks,
      erase annotatedForks = forks ∧
      transition (e, label) g observations (e', label') g' annotatedForks ∧
      invariant (left ++ (e', label') :: right ++ annotatedForks, g')

end MachCSL.Machine.AnnotatedPool
