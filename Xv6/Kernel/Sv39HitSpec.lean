import Xv6.Kernel.Sv39HitDefs

namespace Xv6.Kernel.Sv39Hit
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure FactorSpec : Prop where
  raw : ∀ asid vpn idx ent access mxr doSum,
    program asid vpn idx ent access mxr doSum =
      permission ent access mxr doSum >>= afterPermission vpn idx ent access mxr doSum
  entry_update : ∀ asid vpn idx p2 p1 word access mxr doSum,
    afterPermission vpn idx (entry asid vpn p2 p1 word) access mxr doSum (.PTE_Check_Success ()) =
      SupervisorPteAD.program vpn (PtTree.addr0 p1 vpn) word access mxr doSum >>=
        afterUpdate vpn idx (entry asid vpn p2 p1 word)
  kernel_head : ∀ asid vpn idx p2 p1 ppn perm a d access,
    KptLeaf.Supported access → KptLeaf.Allows perm access → ∀ mxr doSum,
    program asid vpn idx (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d)) access mxr doSum =
      head (KptLeaf.word ppn perm a d) access >>=
        remainder vpn idx (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d))
          (PtTree.addr0 p1 vpn) access mxr doSum
  denied : ∀ asid vpn idx ent access mxr doSum failure,
    permission ent access mxr doSum = pure (.PTE_Check_Failure ((), failure)) →
    program asid vpn idx ent access mxr doSum = pure (.Err (ext_get_ptw_error failure, ()))
  enabled_remainder : ∀ vpn idx ent address access mxr doSum,
    (update_PTE_Bits ent.pte access).isSome = true →
    remainder vpn idx ent address access mxr doSum true =
      (read_pte_exclusive (.Physaddr address) 8 >>=
        SupervisorPteAD.afterRead vpn address access mxr doSum) >>= afterUpdate vpn idx ent
  disabled_remainder : ∀ vpn idx ent address access mxr doSum,
    (update_PTE_Bits ent.pte access).isSome = true →
    remainder vpn idx ent address access mxr doSum false =
      pure (.Err (.PTW_PTE_Needs_Update (), ()))
  write_false : ∀ word ext, SupervisorPteAD.afterWrite word ext (.Ok false) =
    internal_error "sys/vmem.sail" 226 "PTE conditional write failed"
  write_error : ∀ word ext error, SupervisorPteAD.afterWrite word ext (.Err error) =
    pure (.Err (.PTW_No_Access (), ext))
  coherent_resume : ∀ asid tree rs vpn ent response,
    TlbCoherence.Coherent asid tree (rs .tlb) →
    (rs .tlb)[TlbCoherence.index vpn]? = some (some ent) → UpdateVariant ent response →
    TlbCoherence.Coherent asid tree
      (updateAfter rs (TlbCoherence.index vpn) ent response .tlb)

structure PlanSpec : Prop where
  head : ∀ environment rs cached access,
    RegisterPlan.Returns (footprint environment) rs (head cached access) (headValue rs cached access) rs
  resume : ∀ environment rs vpn idx ent response, idx < 64 → PtTree.PbmtZero ent.pte →
    RegisterPlan.Returns (footprint environment) rs (afterUpdate vpn idx ent response)
      (updateValue vpn ent response) (updateAfter rs idx ent response)

/-- These native rules leave the exact enabled memory remainder as an
ordinary WP obligation. There is no assumed atomic callback or successful
read/write equation. Shared slot resources can be framed through these rules. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  head : ∀ environment rs asid vpn idx p2 p1 ppn perm a d access,
    KptLeaf.Supported access → KptLeaf.Allows perm access → ∀ mxr doSum
      image fixed whole gen era cpu (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs environment -∗
      (cells capacity era cpu rs environment -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu
          (remainder vpn idx (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d))
            (PtTree.addr0 p1 vpn) access mxr doSum
            (headValue rs (KptLeaf.word ppn perm a d) access) >>= continuation)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu
        (program asid vpn idx (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d))
          access mxr doSum >>= continuation)) post)
  resume : ∀ environment rs vpn idx ent response, idx < 64 → PtTree.PbmtZero ent.pte →
    ∀ image fixed whole gen era cpu (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs environment -∗
      (cells capacity era cpu (updateAfter rs idx ent response) environment -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (updateValue vpn ent response))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (afterUpdate vpn idx ent response >>= continuation)) post)

end Xv6.Kernel.Sv39Hit
