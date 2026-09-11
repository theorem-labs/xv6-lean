import Xv6.Kernel.KernelTextImageDefs

namespace Xv6.Kernel.KernelTextImage
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  source : ∀ a, sourceMap a = listMap ((Xv6.Generated.KernelMaps.codeRuns.map ByteRun.entries).flatten) a
  listedLookup : ∀ run ∈ Xv6.Generated.KernelMaps.codeRuns, ∀ j, j < run.length →
    sourceMap (run.base + (j : Int)) = some (run.byte j)
  lookupListed : ∀ a b, sourceMap a = some b → ∃ run ∈ Xv6.Generated.KernelMaps.codeRuns,
    ∃ j, j < run.length ∧ a = run.base + (j : Int) ∧ b = run.byte j
  textAddress : ∀ a b, sourceMap a = some b →
    KernelDatum.Positive (address a) ∧ KernelTextDatum.AddrIsText (address a)
  byteCount : (Xv6.Generated.KernelMaps.codeRuns.map ByteRun.length).sum = 23748
  mycpu : ∀ i : Fin 14, ∀ j : Fin (MycpuFetchBytes.width i),
    ∃ b, sourceMap (MycpuDecode.base + ((MycpuDecode.offset i + j.val : Nat) : Int)) = some b ∧
      value b = nthByte (MycpuFetchBytes.word i) j.val

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  persistent : ∀ era tier, Persistent (text capacity era tier)
  listed : ∀ era tier, iprop(text capacity era tier ⊣⊢ listedText capacity era tier)
  lookup : ∀ era tier a b, sourceMap a = some b →
    iprop(text capacity era tier ⊢ KernelTextDatum.byte capacity era tier (address a) .discard (value b))
  physical : ∀ era,
    iprop(⊢ physicalText capacity era -∗ KernelMapStatic.claims capacity era.kernelMap -∗ text capacity era .identity)
  mono : ∀ era tier tier', KernelDatum.Tier.Le tier tier' →
    iprop(text capacity era tier ⊢ text capacity era tier')
  window : ∀ era tier a n (word : BitVec (8*n)),
    (∀ j, j < n → ∃ b, sourceMap (a + (j : Int)) = some b ∧ value b = nthByte word j) →
    iprop(text capacity era tier ⊢ KernelTextDatum.window capacity era tier (address a) n .discard word)
  mycpu : ∀ era tier (shell : MycpuRegimeShell.Capacity GF), shell.translation = capacity →
    iprop(text capacity era tier ⊢ text capacity era tier ∗ MycpuKptFetch.code shell era tier)

end Xv6.Kernel.KernelTextImage
