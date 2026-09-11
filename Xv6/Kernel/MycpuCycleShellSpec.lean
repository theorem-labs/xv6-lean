import Xv6.Kernel.MycpuCycleShellDefs
import MachCSL.Logic.RegisterPlanSpec

namespace Xv6.Kernel.MycpuCycleShell
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  start : ∀ shares rs, rs .hart_state = .HART_ACTIVE () →
    ∀ tick image fixed whole gen era cpu post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      (cells capacity era cpu (started rs) shares -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (run_hart_active 0 >>= finish tick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post)
  finish : ∀ shares rs, rs .hart_state = .HART_ACTIVE () →
    ∀ tick bits image fixed whole gen era cpu (continuation : Unit → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      (∀ after, ⌜completed rs after⌝ -∗ cells capacity era cpu after shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (MycpuCycleShell.finish tick (.Step_Execute (.Retire_Success (), bits)) >>= continuation)) post)
  restart : ∀ shares rs, rs .hart_state = .HART_ACTIVE () →
    ∀ tick bits image fixed whole gen era cpu rr post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜completed rs after⌝ -∗ ▷ (∀ nextTick,
        cells capacity era cpu after shares -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post)) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (MycpuCycleShell.finish tick (.Step_Execute (.Retire_Success (), bits)))) post)

end Xv6.Kernel.MycpuCycleShell
