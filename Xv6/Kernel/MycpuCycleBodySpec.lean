import Xv6.Kernel.MycpuCycleBodyDefs

namespace Xv6.Kernel.MycpuCycleBody
open MycpuMemory
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions TsoContextReadWP

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  store : ∀ slot shares (rs : RegisterFile) region, WriteConfig slot rs region →
    ∀ image fixed whole gen era cpu ξ (old : BitVec 64) rr
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗
      wordPointsto capacity era ξ (address slot rs) (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗
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
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗
      wordPointsto capacity era ξ (address slot rs) dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu (after slot rs word) shares -∗ running capacity era cpu ξ -∗
        wordPointsto capacity era ξ (address slot rs) dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (loadBody slot >>= continuation)) post)

  scalar : ∀ shares (i : Fin 9) image fixed whole gen era cpu rs
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      (cells capacity era cpu (MycpuScalar.after i rs) shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (MycpuScalar.body i >>= continuation)) post)
  ret : ∀ shares (rs : RegisterFile), MycpuReturn.Config rs →
    ∀ image fixed whole gen era cpu (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      (cells capacity era cpu (MycpuReturn.after rs) shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (MycpuReturn.body >>= continuation)) post)

end Xv6.Kernel.MycpuCycleBody
