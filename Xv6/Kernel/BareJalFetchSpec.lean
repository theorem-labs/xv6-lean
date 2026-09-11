import Xv6.Kernel.BareJalFetchDefs

namespace Xv6.Kernel.BareJalFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  factor : program = KptFetch.factor SupervisorBareFetch.program
  unique : ∀ shares, RegisterFootprint.Unique (footprint shares)
  plan : ∀ shares rs word, _get_Misa_C (rs .misa) = 1#1 →
    is_aligned_vaddr (.Virtaddr (rs .PC)) 2 = true →
    Plan (footprint shares) rs (parts (rs .PC) word) program (classified word)
  physical : ∀ shares rs, Config rs → ∀ start address n,
    SupervisorFetchRead.Supported n → is_aligned_vaddr (.Virtaddr address) n = true →
    KernelTextDatum.AddrIsText address →
    SupervisorFetchRead.OneRead (footprint shares) rs address n
      (SupervisorBareFetch.program start address n) (fun word => .FetchBytes_Success word)

structure ResourceSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  persistent : ∀ era pc word, Persistent (code capacity era pc word)
  partition : ∀ era cpu rs shares,
    iprop(cells capacity era cpu rs shares ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs
        [(.PC,shares.pc),(.misa,shares.misa)] ∗
      SupervisorBareFetch.cells capacity.machine era cpu rs shares.bare)
  context : ∀ era ξ address n word,
    iprop(KernelTextDatum.window capacity era .identity address n .discard word ⊢
      TsoContextBytesReadWP.window capacity.machine era ξ address n .discard word)
  text : ∀ era address n word, 0 < n →
    iprop(KernelTextDatum.window capacity era .identity address n .discard word ⊢
      ⌜KernelTextDatum.AddrIsText address⌝)

/-- The chunk primitive and full outer fetch are internally implemented;
no translation, memory result or fetch-success proof is a public input. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  chunk : ∀ shares rs, Config rs → ∀ start address n,
    SupervisorFetchRead.Supported n → is_aligned_vaddr (.Virtaddr address) n = true →
    ∀ image fixed whole gen era cpu ξ (word : BitVec (8*n)) continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ -∗
      KernelTextDatum.window capacity era .identity address n .discard word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextBytesReadWP.running capacity.machine era cpu ξ -∗
        KernelTextDatum.window capacity era .identity address n .discard word -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        RegisterWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.FetchBytes_Success word))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (SupervisorBareFetch.program start address n >>= continuation)) post)
  fetch : ∀ shares rs, Config rs → ∀ word image fixed whole gen era cpu ξ continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ -∗
      code capacity era (rs .PC) word -∗
      finish capacity image fixed whole gen era cpu ξ rs shares word continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post)

end Xv6.Kernel.BareJalFetch
