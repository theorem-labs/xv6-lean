import Xv6.Kernel.MycpuMemoryDefs

namespace Xv6.Kernel.MycpuMemory
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions TsoContextReadWP

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  store : ∀ slot shares (rs : RegisterFile) region, WriteConfig slot rs region →
    ∀ image fixed whole gen era cpu ξ (old : BitVec 64) rr
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs slot shares shares.data -∗ running capacity era cpu ξ -∗
      wordPointsto capacity era ξ (address slot rs) (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs slot shares shares.data -∗ running capacity era cpu ξ -∗
        wordPointsto capacity era ξ (address slot rs) (.own 1) (dataValue slot rs) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (storeBody slot >>= continuation)) post)
  load : ∀ slot shares (rs : RegisterFile) region, ReadConfig slot rs region →
    ∀ image fixed whole gen era cpu ξ dq (word : BitVec 64) rr
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs slot shares (.own 1) -∗ running capacity era cpu ξ -∗
      wordPointsto capacity era ξ (address slot rs) dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu (after slot rs word) slot shares (.own 1) -∗ running capacity era cpu ξ -∗
        wordPointsto capacity era ξ (address slot rs) dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (loadBody slot >>= continuation)) post)

end Xv6.Kernel.MycpuMemory
