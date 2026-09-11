import Xv6.Kernel.MycpuKptBodyDefs

namespace Xv6.Kernel.MycpuKptBody
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec [Platform] : Prop where
  index : ∀ i, routeIndex (route i) = i
  body : ∀ i, MycpuKptBody.body i = routedBody (route i)
  raAddress : ∀ entrySP, slotAddress entrySP .ra = entrySP - 8#64
  s0Address : ∀ entrySP, slotAddress entrySP .s0 = entrySP - 16#64
  memoryAddress : ∀ i entrySP cpu values kind slot,
    route i = .memory kind slot → StackReady i entrySP cpu values →
    MycpuKptMemory.address cpu values slot = slotAddress entrySP slot
  phaseReady : ∀ i entrySP cpu values,
    HartTp.rget cpu values 2#5 = phaseSP i entrySP → StackReady i entrySP cpu values
  phaseStep : ∀ i entrySP control cpu values words,
    HartTp.rget cpu values 2#5 = phaseSP i entrySP →
    HartTp.rget cpu (afterValues (route i) control cpu values words) 2#5 = nextSP i entrySP
  pc : ∀ i control cpu values, afterControl (route i) control cpu values .PC = control .PC
  nextPC : ∀ i control cpu values, i.val ≠ 13 →
    afterControl (route i) control cpu values .nextPC = control .nextPC
  returnPC : ∀ control cpu values,
    afterControl (route ⟨13, by decide⟩) control cpu values .nextPC =
      MycpuReturn.retPC (HartTp.rget cpu values 1#5)
  storeFalse : MycpuKptMemory.storeTail (.Ok false) = pure (.Retire_Success ())
  storeError : ∀ error, MycpuKptMemory.storeTail (.Err error) = pure error
  loadError : ∀ slot error, MycpuKptMemory.loadTail slot (.Err error) = pure error

/-- Every decoded body is proved from real source packet and virtual-word
resources. Only the genuine returned-body continuation is a WP premise. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  body : ∀ i shares control values, Config i control →
    ∀ entrySP tier ξ words rr image fixed whole gen era cpu (N : Namespace) root,
    StackReady i entrySP cpu values → ∀ (frame : IProp GF)
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      pair capacity era tier ξ entrySP words -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu shares control values N root (route i)
        tier ξ entrySP words rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (MycpuKptBody.body i >>= continuation)) post)

end Xv6.Kernel.MycpuKptBody
