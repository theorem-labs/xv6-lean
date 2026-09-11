import MachCSL.Logic.SupervisorClockDefs
import MachCSL.Logic.RegisterPlanSpec

namespace MachCSL.Logic.SupervisorClock
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  clock : ∀ fp, RegisterFootprint.Unique fp →
    (.mcycle, .own 1) ∈ fp → (.mtime, .own 1) ∈ fp → (.mip, .own 1) ∈ fp →
    ∀ image fixed whole gen era cpu rs (continuation : Unit → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (∀ after, ⌜OffClock rs after⌝ -∗
        RegisterFootprint.cells capacity.era.registers (era.registers cpu) after fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (tick_clock () >>= continuation)) post)

end MachCSL.Logic.SupervisorClock
