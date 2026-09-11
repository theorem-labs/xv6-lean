import Xv6.Kernel.MycpuRegimeShellDefs

namespace Xv6.Kernel.MycpuRegimeShell
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- Checked layout and symbolic-footprint facts, never whole physical-file
claims about registers owned inside the translation resource. -/
structure PureSpec : Prop where
  unique : ∀ shares, RegisterFootprint.Unique (footprint shares)
  length : ∀ shares, (footprint shares).length = 50
  excludesTranslation : ∀ shares r, r ∈ [.satp, .tlb, .pmpcfg_n, .pmpaddr_n] →
    r ∉ (footprint shares).map Prod.fst
  setupFrame : ∀ control r, r ≠ .minstret_increment → started control r = control r
  completedPC : ∀ control after, Completed control after →
    after .PC = control .nextPC ∧ after .nextPC = control .nextPC
  completedStatus : ∀ control after, Completed control after → after .mstatus = control .mstatus

/-- Only the shell is promised. `start` leaves the literal actual active
residual WP visible. A concrete fetch/body proof must discharge it before
any whole-function theorem can be exported. No instruction is assumed to
return successfully, and no invariant-preservation callback is postulated. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  partition : ∀ era cpu regime control values shares,
    iprop(resources capacity era cpu regime control values shares ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry control cpu values) (footprint shares) ∗
      bitFrame capacity era cpu (control .mstatus) ∗ ⌜values 0#5 = 0#64⌝ ∗
      translation capacity era cpu regime)
  disabled : ∀ era cpu regime control values shares,
    iprop(resources capacity era cpu regime control values shares ⊢
      ⌜(_get_Mstatus_SIE (control .mstatus) == 1#1) = false ∧
        entry control cpu values .x4 = HartTp.hartWord cpu⌝)
  start : ∀ shares control values regime, control .hart_state = .HART_ACTIVE () →
    ∀ tick image fixed whole gen era cpu (frame : IProp GF) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu regime control values shares -∗ frame -∗
      (resources capacity era cpu regime (started control) values shares -∗ frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (active tick)) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)
  finish : ∀ shares control values regime, control .hart_state = .HART_ACTIVE () →
    ∀ tick bits image fixed whole gen era cpu (frame : IProp GF)
      (continuation : Unit → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu regime control values shares -∗ frame -∗
      (∀ after, ⌜Completed control after⌝ -∗
        resources capacity era cpu regime after values shares -∗ frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation ())) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (MycpuRegimeShell.finish tick (.Step_Execute (.Retire_Success (), bits)) >>= continuation)) post)
  restart : ∀ shares control values regime, control .hart_state = .HART_ACTIVE () →
    ∀ tick bits image fixed whole gen era cpu rr (frame : IProp GF) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu regime control values shares -∗ frame -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜Completed control after⌝ -∗ ▷ (∀ nextTick,
        resources capacity era cpu regime after values shares -∗ frame -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (MycpuRegimeShell.finish tick (.Step_Execute (.Retire_Success (), bits)))) post)

end Xv6.Kernel.MycpuRegimeShell
