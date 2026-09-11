import Xv6.Kernel.MycpuFetchDefs

namespace Xv6.Kernel.MycpuFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  fetch : ∀ shares rs i region, Config rs i region →
    ∀ image fixed whole gen era cpu ξ dq (continuation : FetchResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity era cpu ξ -∗
      window capacity era ξ dq i -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity era cpu ξ -∗
        window capacity era ξ dq i -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (result i))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (LeanPaperStock.Functions.fetch () >>= continuation)) post)
  fetch_shared : ∀ shares rs i region, Config rs i region →
    ∀ image fixed whole gen era cpu ξ (continuation : FetchResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity era cpu ξ -∗
      shared capacity era -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity era cpu ξ -∗
        shared capacity era -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (result i))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (LeanPaperStock.Functions.fetch () >>= continuation)) post)

end Xv6.Kernel.MycpuFetch
