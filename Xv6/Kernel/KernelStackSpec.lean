import Xv6.Kernel.KernelStackDefs

namespace Xv6.Kernel.KernelStack
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  zero : ∀ era tier ξ sp, iprop(own capacity era tier ξ sp 0 ⊣⊢ emp)
  append : ∀ era tier ξ sp n m,
    iprop(own capacity era tier ξ sp (n + m) ⊣⊢
      own capacity era tier ξ sp n ∗ own capacity era tier ξ (paStk sp n) m)
  split : ∀ era tier ξ sp a n, a ≤ n →
    iprop(own capacity era tier ξ sp n ⊣⊢
      own capacity era tier ξ sp a ∗ own capacity era tier ξ (paStk sp a) (n - a))
  one : ∀ era tier ξ sp,
    iprop(own capacity era tier ξ sp 1 ⊣⊢ ∃ value : BitVec 64,
      KernelDatum.word capacity era tier ξ (paStk sp 1) (.own 1) value)
  two : ∀ era tier ξ sp,
    iprop(own capacity era tier ξ sp 2 ⊣⊢ ∃ first second : BitVec 64,
      KernelDatum.word capacity era tier ξ (paStk sp 1) (.own 1) first ∗
      KernelDatum.word capacity era tier ξ (paStk sp 2) (.own 1) second)
  frame_two : ∀ era tier ξ sp n, 2 ≤ n →
    iprop(own capacity era tier ξ sp n ⊣⊢ ∃ first second : BitVec 64,
      KernelDatum.word capacity era tier ξ (paStk sp 1) (.own 1) first ∗
      KernelDatum.word capacity era tier ξ (paStk sp 2) (.own 1) second ∗
      own capacity era tier ξ (paStk sp 2) (n - 2))
  mono : ∀ era tier tier' ξ sp n, KernelDatum.Tier.Le tier tier' →
    iprop(own capacity era tier ξ sp n ⊢ own capacity era tier' ξ sp n)
  sp_bounds : ∀ era tier ξ sp n, 0 < n →
    iprop(own capacity era tier ξ sp n ⊢ ⌜8 ≤ sp.toNat ∧ sp.toNat < 2^38 + 8⌝)
  sp_nonzero : ∀ era tier ξ sp n, 0 < n →
    iprop(own capacity era tier ξ sp n ⊢ ⌜sp ≠ 0#64⌝)

end Xv6.Kernel.KernelStack
