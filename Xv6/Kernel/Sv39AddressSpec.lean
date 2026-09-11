import Xv6.Kernel.Sv39AddressDefs

namespace Xv6.Kernel.Sv39Address
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  unique : ∀ shares, RegisterFootprint.Unique (footprint shares)
  mode : ∀ shares rs root, Config rs root →
    RegisterPlan.Returns (footprint shares) rs (translationMode .Supervisor) .Sv39 rs
  satp : ∀ shares rs,
    RegisterPlan.Returns (footprint shares) rs (get_satp 39) (rs .satp) rs
  rooted : ∀ rs root, Config rs root →
    (satp_to_asid (k_n := 64) (rs .satp)).zeroExtend 16 = 0#16 ∧
    satp_to_ppn (k_n := 64) (rs .satp) = root
  exception : ∀ access, Supported access → ∀ error,
    translationException access error = pure (fault access error)
  suffix : ∀ rs address access, Supported access → ∀ response,
    RegisterPlan.Returns [] rs (resume address access response) (resumed address access response) rs
  canonical : ∀ shares rs tree, Config rs (PtTree.base tree) → ∀ address access,
    Supported access → Effective rs access → Canonical address →
    Boundary (footprint shares) rs
      (KptTranslate.program 0#16 tree (vpn address) access (mxr rs) (doSum rs))
      (program address access) (resume address access)
  noncanonical : ∀ shares rs root, Config rs root → ∀ address access,
    Supported access → Effective rs access → ¬ Canonical address →
    RegisterPlan.Returns (footprint shares) rs (program address access)
      (.Err (pageFault access, ())) rs

/-- Only the exact native translation-body WP remains at the canonical
boundary; no successful translation value is assumed. The final residue
wrapper will construct this premise from `KptTranslate.nativeSpec`. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  canonical : ∀ shares rs tree, Config rs (PtTree.base tree) → ∀ address access,
    Supported access → Effective rs access → Canonical address →
    ∀ image fixed whole gen era cpu (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu rs shares -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (KptTranslate.program 0#16 tree (vpn address) access (mxr rs) (doSum rs) >>=
            fun response => resume address access response >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address access >>= continuation)) post)
  noncanonical : ∀ shares rs root, Config rs root → ∀ address access,
    Supported access → Effective rs access → ¬ Canonical address →
    ∀ image fixed whole gen era cpu (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu rs shares -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Err (pageFault access, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address access >>= continuation)) post)
  suffix : ∀ address access, Supported access → ∀ response,
    ∀ image fixed whole gen era cpu (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (continuation (resumed address access response))) post -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (resume address access response >>= continuation)) post)

end Xv6.Kernel.Sv39Address
