import Xv6.Kernel.KptTranslateDefs

namespace Xv6.Kernel.KptTranslate
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  factor : ∀ asid tree vpn access mxr doSum,
    program asid tree vpn access mxr doSum =
      lookup_TLB 39 asid vpn >>= dispatch asid tree vpn access mxr doSum
  lookup_mapped : ∀ asid tree tlb vpn p2 p1 ppn permission referenceA referenceD idx ent,
    PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD) →
    TlbCoherence.Coherent asid tree tlb →
    TlbCoherence.lookupValue tlb asid vpn = some (idx, ent) →
    idx = TlbCoherence.index vpn ∧ tlb[idx]? = some (some ent) ∧
      ∃ cachedA cachedD,
        ent = TlbCoherence.entry asid vpn p2 p1 (KptLeaf.word ppn permission cachedA cachedD)
  lookup_plan : ∀ shares rs asid vpn,
    RegisterPlan.Returns (footprint shares) rs (lookup_TLB 39 asid vpn)
      (TlbCoherence.lookupValue (rs .tlb) asid vpn) rs

/-- Actual `translate 39`, including the preceding TLB read and both
empty/foreign-tag misses. Hit residency and its mapped cached leaf are
proved internally from coherence; no successful-lookup premise is input. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  translate : ∀ shares rs asid tree vpn p2 p1 regions, Config rs tree vpn p2 p1 regions →
    ∀ ppn permission referenceA referenceD,
    PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD) →
    TlbCoherence.Coherent asid tree (rs .tlb) →
    ∀ access, KptLeaf.Supported access → KptLeaf.Allows permission access →
    ∀ mxr doSum image fixed whole gen era cpu (N : Namespace) root bound rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tree bound asid vpn p2 p1 ppn
        permission referenceA referenceD access rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program asid tree vpn access mxr doSum >>= continuation)) post)

end Xv6.Kernel.KptTranslate
