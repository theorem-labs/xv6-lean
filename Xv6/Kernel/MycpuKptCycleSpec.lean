import Xv6.Kernel.MycpuKptCycleDefs
import MachCSL.Logic.SupervisorInterruptDefs

namespace Xv6.Kernel.MycpuKptCycle
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

structure PureSpec [Platform] : Prop where
  factor : ∀ stepNo, run_hart_active stepNo =
    (PreSail.readReg .cur_privilege >>= fun privilege => dispatchInterrupt privilege >>= fun pending =>
      match pending with
      | some (intr,priv) => pure (.Step_Pending_Interrupt (intr,priv))
      | none => fetch () >>= MycpuActive.afterFetch stepNo)
  decodePlan : ∀ shares rs i, Config rs →
    RegisterPlan.Returns (footprint shares) rs (MycpuKptFetch.decodeFetch (MycpuKptFetch.result i))
      (MycpuDecode.decoded i) rs
  dispatchPlan : ∀ shares rs, Config rs → (_get_Mstatus_SIE (rs .mstatus) == 1#1) = false →
    RegisterPlan.Returns (footprint shares) rs (PreSail.readReg .cur_privilege >>= dispatchInterrupt) none rs
  preparePlan : ∀ shares control cpu values i, Config control →
    MycpuActive.Prefix (footprint shares) (entry control cpu values)
      (MycpuActive.afterFetch 0 (MycpuKptFetch.result i)) (MycpuActive.executeTail i)
      (entry (Prepared i control) cpu values)
  executeTail : ∀ i, MycpuActive.executeTail i = (MycpuKptBody.body i >>= fun execution =>
    pure (.Step_Execute (execution,MycpuActive.instbits i)))
  preparedEntry : ∀ i control cpu values,
    Prepared i (entry control cpu values) = entry (Prepared i control) cpu values
  fetchConfig : ∀ control, Config control → MycpuKptFetch.Config control
  bodyConfig : ∀ i control, Config control → MycpuKptBody.Config i (Prepared i control)
  startedConfig : ∀ control, Config control → Config (started control)
  bodyConfigStable : ∀ i control cpu values, Config control → Config (bodyControl i control cpu values)
  completedConfig : ∀ i control cpu values after, Config control →
    MycpuRegimeShell.Completed (bodyControl i control cpu values) after → Config after
  nextPC : ∀ i control cpu values, bodyControl i control cpu values .nextPC = MycpuKptCycle.nextPC i control cpu values
  completedPC : ∀ i control cpu values after,
    MycpuRegimeShell.Completed (bodyControl i control cpu values) after →
    after .PC = MycpuKptCycle.nextPC i control cpu values ∧ after .nextPC = MycpuKptCycle.nextPC i control cpu values

/-- Both native rules internally discharge actual fetch, decoder register
reads, landing checks, nextPC write and every body. The final rule also
performs actual setup, success suffix, both clocks and genuine restart. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  active : ∀ shares control values, Config control → ∀ i,
    control .PC = MycpuDecode.address i →
    ∀ entrySP tier ξ words rr image fixed whole gen era cpu (N : Namespace) root,
    MycpuKptBody.StackReady i entrySP cpu values → ∀ (frame : IProp GF)
      (continuation : Step → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ pair capacity era tier ξ entrySP words -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      activeFinish capacity image fixed whole gen era cpu shares control values N root i tier ξ entrySP words rr
        frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (run_hart_active 0 >>= continuation)) post)
  cycle : ∀ shares control values, Config control → ∀ i,
    control .PC = MycpuDecode.address i →
    ∀ entrySP tier ξ words rr tick image fixed whole gen era cpu (N : Namespace) root,
    MycpuKptBody.StackReady i entrySP cpu values → ∀ (frame : IProp GF) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ pair capacity era tier ξ entrySP words -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      cycleFinish capacity image fixed whole gen era cpu shares control values N root i tier ξ entrySP words frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (MachCSL.Machine.cycle tick)) post)

end Xv6.Kernel.MycpuKptCycle
