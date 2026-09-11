import MachCSL.Logic.InvariantDefs

namespace MachCSL.Logic.Invariant
open Iris Iris.BI

structure InvariantSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  allocate : ∀ n : Nat, iprop(⊢ |==> ∃ names : Names, allocated capacity names n)

end MachCSL.Logic.Invariant
