import MachCSL.Logic.StateInterpDefs

/-! Generation-indexed worker expressions and their actual native machine WPs. -/
namespace MachCSL.Logic.DeadThread
open Iris Iris.BI Iris.ProgramLogic MachCSL.Machine

/-- Exact source `RiscvExec.thread_gen`; the power thread has no generation. -/
def threadGeneration : Expr → Option Nat
  | .hart generation _ _ => some generation
  | .uart generation => some generation
  | .disk generation => some generation
  | .plic generation => some generation
  | .power => none

/-- Native NotStuck WP for the same concrete image and fixed state interpretation. -/
def threadWP {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage)
    (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (e : Expr) (post : Empty → IProp GF) : IProp GF :=
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  iprop(WP e @ Stuckness.NotStuck; ⊤ {{ post }})

end MachCSL.Logic.DeadThread
