import MachCSL.Logic.SupervisorPmpDefs
import MachCSL.Logic.RegisterPlanSpec

namespace MachCSL.Logic.SupervisorPmp
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  check : ∀ image fixed whole gen era cpu rootPpn address width,
    0 < width → ramLow ≤ address.toNat → address.toNat + width ≤ ramHigh →
    ∀ access, Machine.SupervisorPmp.Supported access →
    ∀ (continuation : Option ExceptionType → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      config capacity.era.registers (era.registers cpu) rootPpn -∗
      (config capacity.era.registers (era.registers cpu) rootPpn -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation none)) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (pmpCheck (.Physaddr address) width access .Supervisor >>= continuation)) post)

end MachCSL.Logic.SupervisorPmp
