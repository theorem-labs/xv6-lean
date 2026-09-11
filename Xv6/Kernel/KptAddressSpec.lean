import Xv6.Kernel.KptAddressDefs

namespace Xv6.Kernel.KptAddress
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  unique : ∀ shares, RegisterFootprint.Unique (footprint shares)
  outer : ∀ rs data root, Ambient rs → KptResidue.SatpRooted root data.satp →
    Sv39Address.Config (prepare rs data) root
  controls : ∀ rs data, Ambient rs → MachCSL.Machine.SupervisorPmp.TorRam (prepare rs data) →
    KptHardware.Controls (prepare rs data)
  effective : ∀ rs data access, Sv39Address.Effective rs access →
    Sv39Address.Effective (prepare rs data) access
  after : ∀ rs data address ppn permission tree p2 p1 a d branch,
    KptTranslate.after (prepare rs data) 0#16 (Sv39Address.vpn address) p2 p1 ppn permission branch =
      prepare rs (afterData rs data address ppn permission (.translated tree p2 p1 a d branch))
  preserved : ∀ rs data address ppn permission outcome,
    let next := afterData rs data address ppn permission outcome
    next.satp = data.satp ∧ next.cfg = data.cfg ∧ next.addr = data.addr

/-- Concrete source residue opening/closing and an exact nine-cell
partition. These resources have native implementations, not allocation or
restoration assumptions in the eventual translation rule. -/
structure ResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  open_residue : ∀ era cpu rs (N : Namespace) root,
    iprop(KptResidue.residue capacity era cpu N root ⊢ ∃ data, opened capacity era cpu rs N root data)
  close_residue : ∀ era cpu rs (N : Namespace) root data,
    iprop(opened capacity era cpu rs N root data ⊢ KptResidue.residue capacity era cpu N root)
  partition : ∀ era cpu rs shares data,
    iprop(cells capacity era cpu (prepare rs data) shares ⊣⊢
      auxiliaryCells capacity era cpu rs shares ∗ dataCells capacity era cpu data)

/-- Full actual supervisor `translateAddr`, including noncanonical faults.
SATP, initial TLB, PMP vectors, snapshot, publication bound and credential
come from the source residue. Native mapping ownership supplies the path and
all address-specific hardware conditions. No body-WP premise remains. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  translate : ∀ shares rs, Ambient rs → ∀ address ppn permission access,
    KptLeaf.Supported access → KptLeaf.Allows permission access → Sv39Address.Effective rs access →
    ∀ image fixed whole gen era cpu (N : Namespace) root rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      auxiliaryCells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      KptShared.mapAt capacity era (Sv39Address.vpn address) ppn permission -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root address ppn permission access rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program address access >>= continuation)) post)

end Xv6.Kernel.KptAddress
