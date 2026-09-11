import MachCSL.Logic.IcacheTypeGhostDefs
import MachCSL.Logic.LogTxDefs
import MachCSL.Logic.IcacheSlotCouplingDefs

/-! Exact native claim and freeze shelters from `InodeRegion.v:1821–1905,
2564–2630`. The transaction and share remain fields of the raw column. -/
namespace MachCSL.Logic.IcacheShelter
open Iris Iris.BI IcacheRefLedger

def cty_pin : ClaimCell → Option (Nat × Qp)
  | some (.excl claim) => some claim.car.2
  | _ => none

variable {GF : BundledGFunctors}

def ireg_cpin (transactions : LogTx.Capacity GF) (txName : GName) (c : ClaimCell) : IProp GF :=
  LogTx.tx_pin_o transactions txName (cty_pin c)

def ireg_fpin (transactions : LogTx.Capacity GF) (txName : GName) (rg : FreezeIndex) : IProp GF :=
  LogTx.tx_pin transactions txName rg.2.1 rg.2.2

def ireg_fsh (types : IcacheTypeGhost.Capacity GF) (transactions : LogTx.Capacity GF)
    (bootName txName : GName) (f : FreezeCell) : IProp GF :=
  match f with
  | some (.excl phase) => match phase.car with
    | .off => iprop(True)
    | .pre rg => iprop(IcacheTypeGhost.ireg_regime types bootName rg.1 ∗ ireg_fpin transactions txName rg)
    | .post rg => iprop(IcacheTypeGhost.ireg_regime types bootName rg.1 ∗ ireg_fpin transactions txName rg)
  | _ => iprop(IcacheTypeGhost.ireg_open types bootName ∨ IcacheTypeGhost.ireg_boot types bootName)

def ireg_shp (types : IcacheTypeGhost.Capacity GF) (transactions : LogTx.Capacity GF)
    (bootName txName : GName) (c : ClaimCell) (f : FreezeCell) : IProp GF :=
  iprop(ireg_fsh types transactions bootName txName f ∗ ireg_cpin transactions txName c)

end MachCSL.Logic.IcacheShelter
