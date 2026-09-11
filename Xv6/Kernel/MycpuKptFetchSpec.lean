import Xv6.Kernel.MycpuKptFetchDefs
import Xv6.Kernel.KptFetchSpec

namespace Xv6.Kernel.MycpuKptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  unique : ∀ shares, RegisterFootprint.Unique (footprint shares)
  counts : ∀ shares, (footprint shares).length = 7 ∧ (remainderFootprint shares).length = 43
  members : ∀ shares cell, cell ∈ footprint shares → cell ∈ MycpuRegimeShell.footprint shares
  config : ∀ control cpu values, Config control → SupervisorBits.MsFacts (control .mstatus) →
    KptFetch.Config (entry control cpu values)
  sourceConfig : ∀ control, control .cur_privilege = .Supervisor →
    control .pma_regions = pmaBoot → control .htif_tohost_base = none →
    control .misa = 0x800000000014112d#64 → control .menvcfg = 0xa000000000000000#64 → Config control
  image : ∀ i : Fin 14, readBytes (loadedRam Xv6.Machine.bootImage)
    (MycpuDecode.address i) (MycpuFetchBytes.width i) = some (MycpuFetchBytes.word i)
  coverage :
    ((List.ofFn (fun i : Fin 14 => (List.range (MycpuFetchBytes.width i)).map
      (MycpuDecode.offset i + ·))).flatten).eraseDups = List.range 34
  chunks : ∀ i : Fin 14, KptFetch.chunks (MycpuDecode.address i) (result i) = [MycpuDecode.address i]
  decode : ∀ i : Fin 14, decodeFetch (result i) = MycpuDecode.decode i
  decoded : ∀ i : Fin 14,
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (MycpuDecode.snapshot i) 1000 (decodeFetch (result i)) =
      some (MycpuDecode.decoded i)

structure ResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  persistent : ∀ era tier, Persistent (code capacity era tier)
  timeless : ∀ era tier, Timeless (code capacity era tier)
  window : ∀ era tier i, iprop(code capacity era tier ⊢ MycpuKptFetch.window capacity era tier i)
  instruction : ∀ era tier i, iprop(code capacity era tier ⊢
    KptFetch.instrBytes capacity.translation era tier (MycpuDecode.address i) (result i))
  partition : ∀ era cpu control values shares N root,
    iprop(packet capacity era cpu (.kpt N root) control values shares ⊣⊢
      KptFetch.cells capacity.translation era cpu (entry control cpu values) (fetchShares shares) ∗
      packetFrame capacity era cpu control values shares ∗ KptResidue.residue capacity.translation era cpu N root)

/-- Actual fetch of one of all fourteen indexed instructions from the same
source packet. Code is a native virtual RX/pristine bundle; no physical-window,
translation/body-WP, successful decoder or memory-response premise is input. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  fetch : ∀ shares control values, Config control → ∀ i,
    control .PC = MycpuDecode.address i →
    ∀ tier image fixed whole gen era cpu (N : Namespace) root rr (frame : IProp GF)
      (continuation : FetchResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu control values shares N root tier i rr frame continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post)

end Xv6.Kernel.MycpuKptFetch
