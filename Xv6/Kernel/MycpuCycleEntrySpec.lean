import Xv6.Kernel.MycpuCycleEntryDefs

namespace Xv6.Kernel.MycpuCycleEntry
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open TsoContextReadWP MycpuMemory

/-- Four active-step contracts; no field assumes execution-body correctness. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  scalar : ∀ shares rs (i : Fin 9) region, Config rs (MycpuScalar.index i) region →
    ∀ image fixed whole gen era cpu ξ rr stepNo (continuation : Step → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ fetchView, cells capacity era cpu (scalarAfter i rs) shares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result (MycpuScalar.index i)))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (run_hart_active stepNo >>= continuation)) post)
  store : ∀ slot shares rs fetchRegion dataRegion,
    Config rs (storeIndex slot) fetchRegion → WriteConfig slot rs dataRegion →
    ∀ image fixed whole gen era cpu ξ (old : BitVec 64) rr stepNo
      (continuation : Step → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      wordPointsto capacity era ξ (address slot rs) (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ (∀ fetchView dataView, cells capacity era cpu (prepared (storeIndex slot) rs) shares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        wordPointsto capacity era ξ (address slot rs) (.own 1) (dataValue slot rs) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) dataView -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result (storeIndex slot)))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (run_hart_active stepNo >>= continuation)) post)
  load : ∀ slot shares rs fetchRegion dataRegion,
    Config rs (loadIndex slot) fetchRegion → ReadConfig slot rs dataRegion →
    ∀ image fixed whole gen era cpu ξ dq (word : BitVec 64) rr stepNo
      (continuation : Step → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      wordPointsto capacity era ξ (address slot rs) dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ (∀ fetchView dataView, cells capacity era cpu (loadAfter slot rs word) shares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        wordPointsto capacity era ξ (address slot rs) dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) dataView -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result (loadIndex slot)))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (run_hart_active stepNo >>= continuation)) post)
  ret : ∀ shares rs region, Config rs ⟨13, by decide⟩ region → MycpuReturn.Config rs →
    ∀ image fixed whole gen era cpu ξ rr stepNo (continuation : Step → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ fetchView, cells capacity era cpu (returnAfter rs) shares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result ⟨13, by decide⟩))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (run_hart_active stepNo >>= continuation)) post)

end Xv6.Kernel.MycpuCycleEntry
