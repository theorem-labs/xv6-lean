import MachCSL.Logic.DeadThreadDefs
import MachCSL.Logic.TsoReadDefs

/-! Source HartBarrier.v's two client obligations, on the actual machine. -/
namespace MachCSL.Logic.BarrierWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

abbrev threadWP := @DeadThread.threadWP

def barrierAt (m : SailM α) : Option barrier_kind :=
  match m with
  | .impure (.barrier kind) _ => some kind
  | _ => none

def barrierResume (m : SailM α) : SailM α :=
  match m with
  | .impure (.barrier _) k => k ()
  | _ => m

def afterBarrier (g : State) (cpu : CPU) (kind : barrier_kind) : State :=
  TsoRead.advanceView g cpu (fencePost (hartAgent cpu) g.log (fenceDrains kind) (g.views cpu))

/-- Exact source ghost_step: access to the live heap and TSO bundle, without
a drain bound or a view receipt. -/
def ghostStep {GF : BundledGFunctors} (capacity : Era.Capacity GF) (era : Era.Record)
    (P Q : IProp GF) : IProp GF :=
  iprop(∀ g : State, Era.heapInterpAt capacity era g -∗
    Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes g -∗ P ==∗
    Era.heapInterpAt capacity era g ∗
    Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes g ∗ Q)

/-- Exact source pub_step. The bound concerns this author's own publications;
it is not a claim that this CPU has reached the global log length. -/
def pubStep {GF : BundledGFunctors} (capacity : Era.Capacity GF) (era : Era.Record)
    (cpu : CPU) (P Q : IProp GF) : IProp GF :=
  iprop(∀ g : State, ⌜ownPub (hartAgent cpu) g.log ≤ g.views cpu⌝ -∗
    Tso.Views.viewLB capacity.views era.views era.logLength (hartAgent cpu) (g.views cpu) -∗
    Era.heapInterpAt capacity era g -∗
    Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes g -∗ P ==∗
    Era.heapInterpAt capacity era g ∗
    Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes g ∗ Q)

end MachCSL.Logic.BarrierWP
