import MachCSL.Logic.RegisterFootprintDefs

namespace MachCSL.Logic.RegisterFootprint
open Iris Iris.BI MachCSL.Machine

structure Spec {GF : BundledGFunctors} (capacity : Registers.Capacity GF) : Prop where
  read : ∀ γ rs footprint r dq, (r, dq) ∈ footprint →
    iprop(⊢ cells capacity γ rs footprint -∗
      Registers.regPointsto capacity γ r dq (rs r) ∗
      (Registers.regPointsto capacity γ r dq (rs r) -∗ cells capacity γ rs footprint))
  write : ∀ γ rs footprint r, Unique footprint → (r, .own 1) ∈ footprint →
    iprop(⊢ cells capacity γ rs footprint -∗
      Registers.regPointsto capacity γ r (.own 1) (rs r) ∗
      (∀ value : RegisterType r, Registers.regPointsto capacity γ r (.own 1) value -∗
        cells capacity γ (Sail.Registers.write rs r value) footprint))

end MachCSL.Logic.RegisterFootprint
