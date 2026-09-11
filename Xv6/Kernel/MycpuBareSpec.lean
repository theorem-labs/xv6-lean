import Xv6.Kernel.MycpuBareDefs

namespace Xv6.Kernel.MycpuBare
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open TsoContextReadWP

/-- Complete actual Bare function CPS, with only the returned cycle left to the caller. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  function : ∀ shares frameShares entry, EntryConfig entry →
    ∀ image fixed whole gen era cpu ξ (oldRA oldS0 : BitVec 64) rr initialTick post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu entry shares -∗ calleeFrame capacity era cpu entry frameShares -∗
      running capacity era cpu ξ -∗ shared capacity era -∗
      stackWords capacity era ξ entry oldRA oldS0 -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜Result entry after⌝ -∗
        cells capacity era cpu after shares -∗ calleeFrame capacity era cpu after frameShares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        stackWords capacity era ξ entry (entry .x1) (entry .x8) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        ∀ nextTick, RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle initialTick)) post)
  hart : ∀ shares frameShares entry, EntryConfig entry →
    ∀ image fixed whole gen era cpu ξ (oldRA oldS0 : BitVec 64) rr initialTick post,
    entry .x4 = BitVec.ofNat 64 cpu.val →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu entry shares -∗ calleeFrame capacity era cpu entry frameShares -∗
      running capacity era cpu ξ -∗ shared capacity era -∗
      stackWords capacity era ξ entry oldRA oldS0 -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜HartResult entry after cpu⌝ -∗
        cells capacity era cpu after shares -∗ calleeFrame capacity era cpu after frameShares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        stackWords capacity era ξ entry (entry .x1) (entry .x8) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        ∀ nextTick, RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle initialTick)) post)

end Xv6.Kernel.MycpuBare
