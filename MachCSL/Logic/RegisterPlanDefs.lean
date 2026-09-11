import MachCSL.Logic.RegisterFootprintDefs

namespace MachCSL.Logic.RegisterPlan
open Iris Iris.BI MachCSL.Machine RegisterFootprint

/-- Finite register-only segments of the actual free Sail tree. Universal
reads need no owned cell; writes require a listed full cell. Memory and
barrier boundaries are handled separately, without hiding their steps. -/
inductive Plan (footprint : Footprint) :
    RegisterFile → SailM α → (α → RegisterFile → Prop) → Prop where
  | pure {rs value Q} (good : Q value rs) : Plan footprint rs (.pure value) Q
  | read {rs r dq k Q} (member : (r, dq) ∈ footprint)
      (rest : Plan footprint rs (k (rs r)) Q) :
      Plan footprint rs (.impure (.readReg r) k) Q
  | readAny {rs r k Q} (rest : ∀ value : RegisterType r, Plan footprint rs (k value) Q) :
      Plan footprint rs (.impure (.readReg r) k) Q
  | write {rs r value k Q} (member : (r, .own 1) ∈ footprint)
      (rest : Plan footprint (Sail.Registers.write rs r value) (k ()) Q) :
      Plan footprint rs (.impure (.writeReg r value) k) Q

abbrev Returns (footprint : Footprint) (rs : RegisterFile) (program : SailM α)
    (value : α) (after : RegisterFile) : Prop :=
  Plan footprint rs program (fun result file => result = value ∧ file = after)

end MachCSL.Logic.RegisterPlan
