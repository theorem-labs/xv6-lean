import Xv6.Kernel.PushOffCsrDefs
import MachCSL.Logic.RegisterPlanSpec

namespace Xv6.Kernel.PushOffCsr
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure PureSpec [Platform] : Prop where
  instruction : PushOffCode.normalized index = .CSRImm (0x100#12, 2#5, .Regidx 15#5, .CSRRC)
  entry : ∀ control cpu values,
    PushOffCsr.entry control cpu (afterValues control values) = after (PushOffCsr.entry control cpu values)
  other : ∀ control values key, key ≠ 15#5 → afterValues control values key = values key
  zero : ∀ control values, afterValues control values 0#5 = values 0#5
  pinnedTP : ∀ control cpu values,
    HartTp.rget cpu (afterValues control values) HartTp.tp = HartTp.hartWord cpu
  plan : ∀ fp rs privShare misaShare,
    (.cur_privilege, privShare) ∈ fp → (.misa, misaShare) ∈ fp →
    (.mstatus, .own 1) ∈ fp → (.x15, .own 1) ∈ fp → Config rs →
    SupervisorBits.MsFacts (rs .mstatus) → _get_Mstatus_SIE (rs .mstatus) = 0#1 →
    RegisterPlan.Returns fp rs PushOffCsr.body (.Retire_Success ()) (after rs)

/-- Same-regime native body. The actual owned packet derives mstatus facts
and SIE=0; callers do not assume legalization, CSR success or a component WP. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  body : ∀ shares control values, Config control →
    ∀ image fixed whole gen era cpu regime (frame : IProp GF)
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values shares -∗ frame -∗
      (resources capacity era cpu regime control values shares frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (PushOffCsr.body >>= continuation)) post)

end Xv6.Kernel.PushOffCsr
