import MachCSL.Logic.IcacheEscrowTokensDefs

namespace MachCSL.Logic.IcacheEscrowTokens
open Iris Iris.BI

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  ticketExcl : ∀ gr, iprop(⊢ redeem_ticketA capacity gr -∗ redeem_ticketA capacity gr -∗ False)
  corpseExcl : ∀ name z left right, iprop(⊢ crp_elem capacity name z left -∗ crp_elem capacity name z right -∗ False)
  agree : ∀ name z ge gr ge' gr', iprop(⊢ reg_half capacity name z ge gr -∗
    reg_half capacity name z ge' gr' -∗ ⌜ge = ge' ∧ gr = gr'⌝)
  exclude : ∀ name z ge gr ge' gr', iprop(⊢ reg_full capacity name z ge gr -∗
    reg_half capacity name z ge' gr' -∗ False)
  split : ∀ name z ge gr, iprop(reg_full capacity name z ge gr ⊣⊢
    reg_half capacity name z ge gr ∗ reg_half capacity name z ge gr)
  pending : ∀ name z ge gr, iprop(⊢ reg_half capacity name z ge gr -∗
    committedA capacity ge -∗ region_pending capacity name z)

end MachCSL.Logic.IcacheEscrowTokens
