import Xv6.Kernel.PushOffMycpuCallsDefs

namespace Xv6.Kernel.PushOffMycpuCalls
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  encoding : ∀ site, KptJal.encoding (immediate site) = encoding site
  target : ∀ site, KptJal.target (pc site) (immediate site) = MycpuDecode.address ⟨0, by decide⟩
  aligned : ∀ site, is_aligned_vaddr (.Virtaddr (pc site)) 2 = true
  bytes : ∀ site (j : Nat), j < 4 → ∃ b,
    KernelTextImage.sourceMap (address site + (j : Int)) = some b ∧
      KernelTextImage.value b = nthByte (PushOffMycpuCalls.encoding site) j

/-- Actual source text supplies both push_off JAL-x1 sites. No default byte,
assumed decoder success or caller code-resource premise is introduced. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  code : ∀ era tier site,
    iprop(KernelTextImage.text capacity.translation era .identity ⊢
      KernelTextImage.text capacity.translation era .identity ∗
      KptJal.code capacity era tier (pc site) (immediate site))

end Xv6.Kernel.PushOffMycpuCalls
