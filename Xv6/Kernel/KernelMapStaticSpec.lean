import Xv6.Kernel.KernelMapStaticDefs

namespace Xv6.Kernel.KernelMapStatic
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

structure PureSpec : Prop where
  region_lookup : ∀ lo n permission vpn, lo + n ≤ 2^27 →
    (region lo n permission)[vpn]? =
      if lo ≤ vpn.toNat ∧ vpn.toNat < lo + n then some (identityPPN vpn, permission) else none
  lookup : ∀ vpn, initialMap[vpn]? = (classify vpn).map (fun permission => (identityPPN vpn, permission))
  cases : ∀ vpn permission, Static vpn permission ↔
    (0x80000 ≤ vpn.toNat ∧ vpn.toNat < 0x80007 ∧ permission = .rx) ∨
    (((0x80007 ≤ vpn.toNat ∧ vpn.toNat < 0x88000) ∨
      (0xc000 ≤ vpn.toNat ∧ vpn.toNat < 0x10002)) ∧ permission = .rw)
  bound : ∀ vpn permission, Static vpn permission → vpn.toNat < 0x88000
  identity : ∀ va, KernelDatum.Positive va →
    KernelDatum.physical (identityPPN (KernelDatum.vpn va)) va = va
  text_class : ∀ va, 0x80000000 ≤ va.toNat → va.toNat < 0x80007000 →
    Static (KernelDatum.vpn va) .rx
  data_class : ∀ va, 0x80007000 ≤ va.toNat → va.toNat < 0x88000000 →
    Static (KernelDatum.vpn va) .rw

/-- Native allocation and lookup at the supplied map name. There is no
physical-tree, concrete-era installation or boot-reachability conclusion. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  persistent : ∀ γ, Persistent (claims capacity γ)
  timeless : ∀ γ, Timeless (authority capacity γ)
  allocate : ∀ frame : IProp GF, iprop(frame ⊢ |==> ∃ γ,
    authority capacity γ ∗ claims capacity γ ∗ frame)
  lookup : ∀ γ vpn permission, Static vpn permission →
    iprop(claims capacity γ ⊢ KptGhost.mapAt capacity.ghost γ vpn (identityPPN vpn) permission)
  identify : ∀ γ vpn ppn permission,
    iprop(⊢ authority capacity γ -∗ KptGhost.mapAt capacity.ghost γ vpn ppn permission -∗
      ⌜Static vpn permission ∧ ppn = identityPPN vpn⌝)

end Xv6.Kernel.KernelMapStatic
