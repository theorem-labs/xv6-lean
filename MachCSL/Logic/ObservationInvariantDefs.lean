import MachCSL.Logic.PowerGhostDefs
import Iris.Instances.Lib.Invariants

namespace MachCSL.Logic.ObservationInvariant
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]

/-- Fixed trace custody, shared by all eras and by UART and power actors.
The ledger predicate is a client choice, not an assertion of trace safety. -/
def ledger (capacity : PowerGhost.Capacity GF) (N : Namespace) (γ : GName)
    (R : List Observation → IProp GF) : IProp GF :=
  inv N (PowerGhost.obsLedger capacity γ R)

def trivial (capacity : PowerGhost.Capacity GF) (N : Namespace) (γ : GName) : IProp GF :=
  ledger capacity N γ (fun _ => iprop(True))

end MachCSL.Logic.ObservationInvariant
