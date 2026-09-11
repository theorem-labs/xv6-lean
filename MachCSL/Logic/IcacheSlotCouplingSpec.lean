import MachCSL.Logic.IcacheSlotCouplingDefs

namespace MachCSL.Logic.IcacheSlotCoupling
open Iris Iris.BI Xv6.Fs IcacheRefLedger
variable {GF : BundledGFunctors}

structure Spec (ledger : IcacheRefLedger.Capacity GF) (coupling : IcacheCoupling.Capacity GF) : Prop where
  mint : ∀ g b z c r f n d, d.type.toNat ≠ 0 → (b = false → c = none) →
    iprop(ireg_rcol ledger g z c r f n d ⊢ |==>
      ((∃ r', ireg_rcol ledger g z c r' f (n + 1) d) ∗ runit ledger g b z))
  spend : ∀ g b z c r f n d,
    iprop(ireg_rcol ledger g z c r f (n + 1) d ∗ runit ledger g b z ⊢ |==>
      ∃ r', ireg_rcol ledger g z c r' f n d)
  mirrorOff : ∀ names z f, frz_preb f = false →
    iprop(ireg_frzc coupling names z f ⊣⊢ IcacheCoupling.frzm_h coupling names z false)
  boot : ∀ g names inums records,
    iprop(IcacheRefLedger.bootRows ledger g inums ∗
      IcacheCoupling.bootCounts coupling names inums ∗ IcacheCoupling.bootMirrors coupling names inums ⊢
      bootRows ledger coupling g names inums records)

end MachCSL.Logic.IcacheSlotCoupling
