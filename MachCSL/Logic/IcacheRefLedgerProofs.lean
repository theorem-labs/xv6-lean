import MachCSL.Logic.IcacheRefLedgerAlgebraProofs

namespace MachCSL.Logic.IcacheRefLedger
open Iris Iris.Std Iris.CMRA Iris.BI
open scoped CommMonoidLike
variable {GF : BundledGFunctors} (capacity : Capacity GF) (g : GName)

instance link_auth_e_timeless i a : Timeless (link_auth_e capacity g i a) := by unfold link_auth_e; infer_instance
instance link_frag_e_timeless i a : Timeless (link_frag_e capacity g i a) := by unfold link_frag_e; infer_instance
instance link_auth_timeless i c r f rc : Timeless (link_auth capacity g i c r f rc) := by unfold link_auth; infer_instance
instance iclaim_timeless i ty t q : Timeless (iclaim capacity g i ty t q) := by unfold iclaim; infer_instance
instance runit_plain_timeless i : Timeless (runit_plain capacity g i) := by unfold runit_plain; infer_instance
instance runit_claim_timeless i : Timeless (runit_claim capacity g i) := by unfold runit_claim; infer_instance
instance runit_timeless b i : Timeless (runit capacity g b i) := by unfold runit; split <;> infer_instance
instance runit_any_timeless i : Timeless (runit_any capacity g i) := by unfold runit_any; infer_instance
instance ifreeze_timeless p i : Timeless (ifreeze capacity g p i) := by unfold ifreeze; infer_instance
instance ifreeze_off_timeless i : Timeless (ifreeze_off capacity g i) := by unfold ifreeze_off; infer_instance
instance ifreeze_pre_timeless index i : Timeless (ifreeze_pre capacity g index i) := by unfold ifreeze_pre; infer_instance
instance ifreeze_post_timeless index i : Timeless (ifreeze_post capacity g index i) := by unfold ifreeze_post; infer_instance

theorem runit_any_intro i : runit capacity g false i ⊢ runit_any capacity g i := .rfl

theorem link_agree_valid i a b : iprop(link_auth_e capacity g i a ∗ link_frag_e capacity g i b ⊢ ⌜b ≼ a ∧ ✓ a⌝) := by
  unfold link_auth_e link_frag_e
  iintro ⟨Ha, Hf⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.ledger) $$ [$Ha $Hf]
  ipureintro
  exact both_valid i a b valid

theorem link_agree_e i a b : iprop(link_auth_e capacity g i a ∗ link_frag_e capacity g i b ⊢ ⌜b ≼ a⌝) := by
  iintro H
  ihave %facts := link_agree_valid capacity g i a b $$ H
  ipureintro; exact facts.1

theorem link_agree i c r c' r' f rc :
    iprop(link_auth capacity g i c r f rc ∗ link_frag_e capacity g i (lelem c' r') ⊢ ⌜r' ≤ r⌝) := by
  unfold link_auth
  iintro H
  ihave %sub := link_agree_e capacity g i _ _ $$ H
  ipureintro
  exact ref_inclusion c r f rc c' r' sub

theorem link_r_ge i c r f rc : iprop(link_auth capacity g i c r f rc ∗ runit_plain capacity g i ⊢ ⌜1 ≤ r⌝) :=
  link_agree capacity g i c r none 1 f rc

theorem link_rc_ge i c r f rc : iprop(link_auth capacity g i c r f rc ∗ runit_claim capacity g i ⊢ ⌜1 ≤ rc⌝) := by
  unfold link_auth runit_claim
  iintro H
  ihave %sub := link_agree_e capacity g i _ _ $$ H
  ipureintro
  exact refc_inclusion c r f rc sub

theorem link_runit_ge b i c r f rc : iprop(link_auth capacity g i c r f rc ∗ runit capacity g b i ⊢ ⌜1 ≤ if b then rc else r⌝) := by
  cases b
  · exact link_r_ge capacity g i c r f rc
  · exact link_rc_ge capacity g i c r f rc

theorem link_claim_agree i c r f rc ty t q :
    iprop(link_auth capacity g i c r f rc ∗ iclaim capacity g i ty t q ⊢ ⌜c = claimCell ty t q⌝) := by
  unfold link_auth iclaim
  iintro H
  ihave %facts := link_agree_valid capacity g i _ _ $$ H
  ipureintro
  exact claim_inclusion c r f rc ty t q facts.2 facts.1

theorem link_freeze_agree i c r f rc phase :
    iprop(link_auth capacity g i c r f rc ∗ ifreeze capacity g phase i ⊢ ⌜f = freezeCell phase⌝) := by
  unfold link_auth ifreeze
  iintro H
  ihave %facts := link_agree_valid capacity g i _ _ $$ H
  ipureintro
  exact freeze_inclusion c r f rc phase facts.2 facts.1

theorem ifreeze_excl i p p' : iprop(ifreeze capacity g p i ∗ ifreeze capacity g p' i ⊢ False) := by
  unfold ifreeze link_frag_e
  iintro ⟨H1, H2⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.ledger) $$ [$H1 $H2]
  ipureintro
  exact freeze_frag_invalid i p p' valid

theorem iclaim_excl i ty t q ty' t' q' : iprop(iclaim capacity g i ty t q ∗ iclaim capacity g i ty' t' q' ⊢ False) := by
  unfold iclaim link_frag_e
  iintro ⟨H1, H2⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.ledger) $$ [$H1 $H2]
  ipureintro
  exact claim_frag_invalid i ty t q ty' t' q' valid

theorem link_update_alloc i a a' b' (update : (a, lelem none 0) ~l~> (a', b')) :
    iprop(link_auth_e capacity g i a ⊢ |==> (link_auth_e capacity g i a' ∗ link_frag_e capacity g i b')) := by
  unfold link_auth_e link_frag_e
  iintro Ha
  imod iOwn_update (E := capacity.ledger) (map_update_alloc i a a' b' update) $$ Ha with H
  imodintro
  iapply (iOwn_op (E := capacity.ledger)).mp $$ H

theorem link_update i a b a' b' (update : (a, b) ~l~> (a', b')) :
    iprop(link_auth_e capacity g i a ∗ link_frag_e capacity g i b ⊢ |==>
      (link_auth_e capacity g i a' ∗ link_frag_e capacity g i b')) := by
  unfold link_auth_e link_frag_e
  iintro ⟨Ha, Hf⟩
  imod iOwn_update_op (E := capacity.ledger) (map_update i a b a' b' update) $$ [$Ha $Hf] with H
  imodintro
  iapply (iOwn_op (E := capacity.ledger)).mp $$ H

end MachCSL.Logic.IcacheRefLedger
