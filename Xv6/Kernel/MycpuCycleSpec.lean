import Xv6.Kernel.MycpuCycleDefs

namespace Xv6.Kernel.MycpuCycle
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open TsoContextReadWP MycpuMemory

/-- Actual cycle plus real restart; final obligations concern only the next cycle. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  scalar : ∀ shares rs (i : Fin 9) region, Config rs (MycpuScalar.index i) region →
    ∀ image fixed whole gen era cpu ξ rr tick post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ (∀ fetchView after, ⌜Completed (scalarBeforeFinish i rs) after⌝ -∗
        ∀ nextTick, cells capacity era cpu after shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post)
  store : ∀ slot shares rs fetchRegion dataRegion,
    Config rs (storeIndex slot) fetchRegion → WriteConfig slot rs dataRegion →
    ∀ image fixed whole gen era cpu ξ (old : BitVec 64) rr tick post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      wordPointsto capacity era ξ (address slot rs) (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ fetchView dataView after, ⌜Completed (storeBeforeFinish slot rs) after⌝ -∗
        ∀ nextTick, cells capacity era cpu after shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
        wordPointsto capacity era ξ (address slot rs) (.own 1) (dataValue slot rs) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) dataView -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post)
  load : ∀ slot shares rs fetchRegion dataRegion,
    Config rs (loadIndex slot) fetchRegion → ReadConfig slot rs dataRegion →
    ∀ image fixed whole gen era cpu ξ dq (word : BitVec 64) rr tick post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      wordPointsto capacity era ξ (address slot rs) dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ fetchView dataView after, ⌜Completed (loadBeforeFinish slot rs word) after⌝ -∗
        ∀ nextTick, cells capacity era cpu after shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
        wordPointsto capacity era ξ (address slot rs) dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) dataView -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post)
  ret : ∀ shares rs region, Config rs ⟨13, by decide⟩ region → MycpuReturn.Config rs →
    ∀ image fixed whole gen era cpu ξ rr tick post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ (∀ fetchView after, ⌜Completed (returnBeforeFinish rs) after⌝ -∗
        ∀ nextTick, cells capacity era cpu after shares -∗ running capacity era cpu ξ -∗ shared capacity era -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) fetchView -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.MycpuCycle
