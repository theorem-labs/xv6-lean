import MachCSL.Logic.RegisterDefs

namespace MachCSL.Logic.RegisterFootprint
open Iris Iris.BI MachCSL.Machine

/-- A finite native register footprint may mix writable, fractional and
discarded cells. The unlisted cells carry no ownership assertion. -/
abbrev Footprint := List (Register × DFrac)

def Unique (footprint : Footprint) : Prop := (footprint.map Prod.fst).Nodup

def cells {GF : BundledGFunctors} (capacity : Registers.Capacity GF)
    (γ : GName) (rs : RegisterFile) : Footprint → IProp GF
  | [] => emp
  | (r, dq) :: rest => iprop(Registers.regPointsto capacity γ r dq (rs r) ∗
      cells capacity γ rs rest)

end MachCSL.Logic.RegisterFootprint
