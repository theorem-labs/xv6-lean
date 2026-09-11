import MachCSL.Logic.TsoViewsDefs
import Iris.Instances.Lib.GhostVar
import MachCSL.Machine.Observations

/-! Fixed generation/start and observation resources from `RiscvPtsto.v`.
These definitions are components only, not the full power/era interpretation. -/
namespace MachCSL.Logic.PowerGhost
open Iris Iris.BI MachCSL.Machine

structure Capacity (GF : BundledGFunctors) where
  sharedNat : ElemG GF MonoNatRF
  observations : GhostVarG GF (List Observation)

structure Names where
  generation : GName
  started : GName
  observations : GName

@[reducible] def Capacity.monoNat {GF : BundledGFunctors} (capacity : Capacity GF)
    (name : GName) : MonoNatG GF := ⟨capacity.sharedNat, name⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def genAuth (γ : GName) (n : Nat) : IProp GF :=
  letI := capacity.monoNat γ
  MonoNat.auth_own γ (.own 1) (.ofNat n)
def genBorn (γ : GName) (generation : Nat) : IProp GF :=
  letI := capacity.monoNat γ
  MonoNat.lb_own γ (.ofNat generation)
def genDead (γ : GName) (generation : Nat) : IProp GF :=
  genBorn capacity γ (generation + 1)

def startCount (g : State) : Nat := g.generation + if g.power then 1 else 0
def startAuth (γ : GName) (n : Nat) : IProp GF := genAuth capacity γ n
def genStarted (γ : GName) (generation : Nat) : IProp GF :=
  genBorn capacity γ (generation + 1)

/-- Only the two counter conjuncts of the source power interpretation. -/
def counterInterp (names : Names) (g : State) : IProp GF :=
  iprop(genAuth capacity names.generation g.generation ∗ startAuth capacity names.started (startCount g))

def obsAuth (γ : GName) (history : List Observation) : IProp GF :=
  letI := capacity.observations
  ghost_var γ (.own (1 : Qp).half) history
def obsFrag (γ : GName) (history : List Observation) : IProp GF := obsAuth capacity γ history

def obsPredTriv (γ : GName) : IProp GF := iprop(∃ h, obsFrag capacity γ h)
def obsLedger (γ : GName) (R : List Observation → IProp GF) : IProp GF :=
  iprop(∃ h, obsFrag capacity γ h ∗ R h)

/-- Exact source past/future trace relation and the actual machine invariant. -/
def obsInterp (γ : GName) (whole : List Observation) (g : State)
    (future : List Observation) : IProp GF :=
  iprop(∃ history : List Observation,
    ⌜history ++ future = whole⌝ ∗ ⌜ObservationsOK history g⌝ ∗ obsAuth capacity γ history)

end MachCSL.Logic.PowerGhost
