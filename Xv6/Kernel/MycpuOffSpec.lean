import Xv6.Kernel.MycpuOffDefs

namespace Xv6.Kernel.MycpuOff
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

/-- Complete disabled Bare body adapter. Neither a duplicate cycle footprint
nor a caller-supplied per-step success/bit/TP premise is accepted. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  function : ∀ shares control values, EntryConfig control →
    ∀ image fixed whole gen era cpu ξ (oldRA oldS0 : BitVec 64) rr initialTick post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ MycpuBare.shared capacity.machine era -∗
      stackWords capacity era ξ control cpu values oldRA oldS0 -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜Result control cpu values after⌝ -∗
        resources capacity era cpu after (returnedMap values after) shares -∗
        TsoContextReadWP.running capacity.machine era cpu ξ -∗ MycpuBare.shared capacity.machine era -∗
        stackWords capacity era ξ control cpu values (values 1#5) (values 8#5) -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle initialTick)) post)

end Xv6.Kernel.MycpuOff
