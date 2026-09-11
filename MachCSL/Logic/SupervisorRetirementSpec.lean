import MachCSL.Logic.SupervisorRetirementDefs
import MachCSL.Logic.RegisterPlanSpec

namespace MachCSL.Logic.SupervisorRetirement
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  setup : ∀ fp, RegisterFootprint.Unique fp → SetupMembers fp →
    ∀ image fixed whole gen era cpu rs (continuation : Unit → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu)
          (setupAfter rs (rs .cur_privilege)) fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (SupervisorRetirement.setup >>= continuation)) post)
  tickPC : ∀ fp, RegisterFootprint.Unique fp →
    ∀ dq, (.nextPC, dq) ∈ fp → (.PC, .own 1) ∈ fp →
    ∀ image fixed whole gen era cpu rs (continuation : Unit → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (tickPCAfter rs) fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (tick_pc () >>= continuation)) post)
  complete : ∀ fp, RegisterFootprint.Unique fp → CompleteMembers fp →
    ∀ image fixed whole gen era cpu rs, rs .hart_state = .HART_ACTIVE () →
    ∀ bits (continuation : Bool → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (completeAfter rs) fp -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation false)) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (postlude (.Step_Execute (.Retire_Success (), bits)) >>= continuation)) post)

end MachCSL.Logic.SupervisorRetirement
