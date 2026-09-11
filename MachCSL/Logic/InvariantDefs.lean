import MachCSL.Logic.StateInterpDefs
import Iris.Instances.Lib.FUpd

/-! Explicit native Iris invariant capacity and allocated runtime names. -/
namespace MachCSL.Logic.Invariant
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

abbrev WorldRF := InvMapF
abbrev EnabledRF := constOF CoPsetDisjL
abbrev DisabledRF := constOF (DisjointLeibnizSet PosSet)
abbrev CreditRF := _root_.Auth.AuthURF (constOF Credit)

/-- Four native invariant-system cameras, separate from their runtime names. -/
structure Capacity (GF : BundledGFunctors) where
  world : ElemG GF WorldRF
  enabled : ElemG GF EnabledRF
  disabled : ElemG GF DisabledRF
  credit : ElemG GF CreditRF

@[reducible] def Capacity.preS {GF : BundledGFunctors} (capacity : Capacity GF) : InvGpreS GF :=
  ⟨⟨capacity.world, capacity.enabled, capacity.disabled⟩, ⟨capacity.credit⟩⟩

structure Names where
  world : GName
  enabled : GName
  disabled : GName
  credit : GName

@[reducible] def Names.wsat {GF : BundledGFunctors} (names : Names) (capacity : Capacity GF) : WsatGS GF :=
  { toWsatGpreS := capacity.preS.toWsatGpreS
    invariant_name := names.world, enabled_name := names.enabled, disabled_name := names.disabled }

@[reducible] def Names.lc {GF : BundledGFunctors} (names : Names) (capacity : Capacity GF) : LcGS .hasLC GF :=
  { toLcGpreS := capacity.preS.toLcGpreS, lc_name := names.credit }

/-- Unlike an arbitrary existential class, this adapter retains the supplied witnesses definitionally. -/
@[reducible] def Names.native {GF : BundledGFunctors} (names : Names) (capacity : Capacity GF) : InvGS GF :=
  { toInvGpreS := capacity.preS, toWsatGS := names.wsat capacity, toLcGS := names.lc capacity }

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def world (names : Names) : IProp GF := wsat (W := names.wsat capacity)
def enabled (names : Names) (mask : CoPset) : IProp GF := ownE (W := names.wsat capacity) mask
def creditSupply (names : Names) (n : Nat) : IProp GF := lc_supply (LC := names.lc capacity) n
def credits (names : Names) (n : Nat) : IProp GF := lc (LC := names.lc capacity) n

def allocated (names : Names) (n : Nat) : IProp GF :=
  iprop(world capacity names ∗ enabled capacity names ⊤ ∗
    creditSupply capacity names n ∗ credits capacity names n)

/-- The same concrete image-parametric machine instance, with allocated native invariant names. -/
@[reducible] def machineGS [Platform] (machineCapacity : MachineInterp.Capacity GF)
    (names : Names) (image : Machine.BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Machine.Observation) :
    @IrisGS_gen .hasLC Machine.Expr Empty Machine.State Machine.Observation
      (Machine.language image) GF := by
  letI := names.native capacity
  exact MachineInterp.irisGS machineCapacity image fixed whole

end MachCSL.Logic.Invariant
