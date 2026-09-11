import Xv6.Kernel.MycpuKptMemoryDefs

namespace Xv6.Kernel.MycpuKptMemory
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec [Platform] : Prop where
  storeBody : ∀ slot, body .store slot =
    execute_STORE (MycpuMemory.immediate slot) (MycpuMemory.dataIndex slot) (.Regidx 2#5) 8
  loadBody : ∀ slot, body .load slot =
    execute_LOAD (MycpuMemory.immediate slot) (.Regidx 2#5) (MycpuMemory.dataIndex slot) false 8
  storeFactor : ∀ slot, body .store slot = (do
    let new ← rX_bits (MycpuMemory.dataIndex slot)
    let sp ← rX_bits (.Regidx 2#5)
    KptMemory.program .store (sp + MycpuMemory.offset slot) new >>= storeTail)
  loadFactor : ∀ slot, body .load slot = (do
    let sp ← rX_bits (.Regidx 2#5)
    KptMemory.program .load (sp + MycpuMemory.offset slot) 0#64 >>= loadTail slot)
  storeFalse : storeTail (.Ok false) = pure (.Retire_Success ())
  storeError : ∀ error, storeTail (.Err error) = pure error
  loadError : ∀ slot error, loadTail slot (.Err error) = pure error
  footprintUnique : ∀ shares slot, RegisterFootprint.Unique (footprint shares slot)
  footprintCounts : ∀ shares slot, (footprint shares slot).length = 7 ∧ (remainderFootprint shares slot).length = 43
  footprintMembers : ∀ shares slot cell, cell ∈ footprint shares slot → cell ∈ MycpuRegimeShell.footprint shares
  ambient : ∀ control cpu values, Config control → SupervisorBits.MsFacts (control .mstatus) →
    KptMemory.Ambient (entry control cpu values)
  mapOther : ∀ kind slot values old i, i ≠ index slot → afterMap kind slot values old i = values i
  afterSP : ∀ kind slot cpu values old, HartTp.rget cpu (afterMap kind slot values old) 2#5 = HartTp.rget cpu values 2#5
  afterAddress : ∀ kind slot cpu values old other,
    address cpu (afterMap kind slot values old) other = address cpu values other

/-- Concrete instruction-body WPs. Native packet ownership supplies the
seven borrowed cells and all forty-three remaining register cells. No memory
WP, physical-word assertion, success proof or selected-view oracle is input. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  body : ∀ shares control values, Config control → ∀ kind slot tier ξ dq old rr,
    (kind = .store → dq = .own 1) →
    ∀ image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF)
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatum.word capacity.translation era tier ξ (address cpu values slot) dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu control values shares N root kind slot tier ξ dq old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (MycpuKptMemory.body kind slot >>= continuation)) post)
  pair : ∀ shares control values, Config control → ∀ kind slot tier ξ words rr,
    ∀ image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF)
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      MycpuKptMemory.pair capacity era cpu tier ξ values words -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finishPair capacity image fixed whole gen era cpu control values shares N root kind slot tier ξ words rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (MycpuKptMemory.body kind slot >>= continuation)) post)

end Xv6.Kernel.MycpuKptMemory
