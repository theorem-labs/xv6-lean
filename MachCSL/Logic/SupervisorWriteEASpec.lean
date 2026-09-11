import MachCSL.Logic.SupervisorWriteEADefs
import MachCSL.Logic.RegisterPlanSpec

namespace MachCSL.Logic.SupervisorWriteEA
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  announce : ∀ shares (rs : RegisterFile) address region, Config rs address region →
    ∀ image fixed whole gen era cpu (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu rs shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (program address >>= continuation)) post)

end MachCSL.Logic.SupervisorWriteEA
