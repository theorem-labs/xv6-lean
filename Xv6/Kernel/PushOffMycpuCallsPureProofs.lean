import Xv6.Kernel.PushOffMycpuCallsSpec

namespace Xv6.Kernel.PushOffMycpuCalls
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

theorem encoding_eq : ∀ site, KptJal.encoding (immediate site) = encoding site := by decide

theorem target : ∀ site, KptJal.target (pc site) (immediate site) = MycpuDecode.address ⟨0, by decide⟩ := by decide

theorem aligned : ∀ site, is_aligned_vaddr (.Virtaddr (pc site)) 2 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem bytes : ∀ site (j : Nat), j < 4 → ∃ b,
    KernelTextImage.sourceMap (address site + (j : Int)) = some b ∧
      KernelTextImage.value b = nthByte (encoding site) j := by
  have finite : ∀ site : Site, ∀ j : Fin 4, ∃ b,
      KernelTextImage.sourceMap (address site + (j.val : Int)) = some b ∧
        KernelTextImage.value b = nthByte (encoding site) j.val := by decide
  exact fun site j bound => finite site ⟨j,bound⟩

theorem pureSpec : PureSpec := ⟨encoding_eq,target,aligned,bytes⟩

end Xv6.Kernel.PushOffMycpuCalls
