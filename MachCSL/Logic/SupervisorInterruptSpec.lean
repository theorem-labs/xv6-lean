import MachCSL.Logic.SupervisorInterruptDefs
import MachCSL.Logic.RegisterPlanSpec

namespace MachCSL.Logic.SupervisorInterrupt
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  dispatch : ∀ image fixed whole gen era cpu shares
    (continuation : Option (InterruptType × Privilege) → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      registers capacity.era.registers (era.registers cpu) shares -∗
      (registers capacity.era.registers (era.registers cpu) shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation none)) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (dispatchInterrupt .Supervisor >>= continuation)) post)

end MachCSL.Logic.SupervisorInterrupt
