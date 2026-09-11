import MachCSL.Logic.RegisterPlanDefs
import MachCSL.Logic.RegisterWPDefs

namespace MachCSL.Logic.RegisterPlan
open Iris Iris.BI MachCSL.Machine RegisterFootprint

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  fold : ∀ {A : Type} footprint, Unique footprint →
    ∀ image fixed whole gen era cpu rs (program : SailM A) Q
      (continuation : A → SailM Unit) post, Plan footprint rs program Q →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity.era.registers (era.registers cpu) rs footprint -∗
      (∀ value after, ⌜Q value after⌝ -∗
        cells capacity.era.registers (era.registers cpu) after footprint -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation value)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post)

end MachCSL.Logic.RegisterPlan
