import MachCSL.Machine.SupervisorPmpProofs
import MachCSL.Logic.RegisterPlanDefs

namespace MachCSL.Logic.SupervisorPmp
open Iris Iris.BI MachCSL.Machine

abbrev Shares := DFrac × DFrac

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.pmpcfg_n, shares.1), (.pmpaddr_n, shares.2)]

abbrev Returns (shares : Shares) (rs : RegisterFile) (program : SailM α)
    (value : α) (after : RegisterFile) : Prop :=
  RegisterPlan.Returns (footprint shares) rs program value after

/-- Source SmodePte.pmp_config: exactly the two full native cells and
entry-zero facts. The source root-PPN index does not affect this predicate. -/
def config {GF : BundledGFunctors} (capacity : Registers.Capacity GF)
    (γ : GName) (_rootPpn : BitVec 44) : IProp GF :=
  iprop(∃ rs : RegisterFile, ⌜Machine.SupervisorPmp.TorRam rs⌝ ∗
    RegisterFootprint.cells capacity γ rs (footprint (.own 1, .own 1)))

end MachCSL.Logic.SupervisorPmp
