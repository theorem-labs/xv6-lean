import MachCSL.Logic.SupervisorBareReadDefs

namespace MachCSL.Logic.SupervisorBareRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open SupervisorRead

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  read : ∀ (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (_config : Config rs address region)
    image fixed whole gen era cpu ξ dq (word : BitVec 64)
    (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address >>= continuation)) post)

end MachCSL.Logic.SupervisorBareRead
