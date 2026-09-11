import MachCSL.Logic.SupervisorAddressDefs
import MachCSL.Logic.RegisterPlanSpec

namespace MachCSL.Logic.SupervisorAddress
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  transform : ∀ (shares : Shares) (rs : RegisterFile) (mode : SATPMode) (_config : Config rs mode)
    (address : BitVec 64) (kind : Kind) image fixed whole gen era cpu
    (continuation : virtaddr → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu rs shares -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Virtaddr address))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address kind >>= continuation)) post)

end MachCSL.Logic.SupervisorAddress
