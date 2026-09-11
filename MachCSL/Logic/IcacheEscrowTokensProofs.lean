import MachCSL.Logic.IcacheEscrowTokensSpec
import Iris.ProofMode

namespace MachCSL.Logic.IcacheEscrowTokens
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance committedA_persistent ge : Persistent (committedA capacity ge) := by
  unfold committedA; letI := capacity.monoNat ge; infer_instance
instance committedA_timeless ge : Timeless (committedA capacity ge) := by
  unfold committedA; letI := capacity.monoNat ge; infer_instance
instance redeem_ticketA_timeless gr : Timeless (redeem_ticketA capacity gr) := by
  unfold redeem_ticketA; infer_instance
instance reg_auth_timeless name rows : Timeless (reg_auth capacity name rows) := by
  unfold reg_auth; letI := capacity.registry; infer_instance
instance reg_elem_timeless name dq z pair : Timeless (reg_elem capacity name dq z pair) := by
  unfold reg_elem; letI := capacity.registry; infer_instance
instance reg_half_timeless name z ge gr : Timeless (reg_half capacity name z ge gr) := by
  unfold reg_half; infer_instance
instance reg_full_timeless name z ge gr : Timeless (reg_full capacity name z ge gr) := by
  unfold reg_full; infer_instance
instance crp_auth_timeless name rows : Timeless (crp_auth capacity name rows) := by
  unfold crp_auth; letI := capacity.corpse; infer_instance
instance crp_elemQ_timeless name dq z value : Timeless (crp_elemQ capacity name dq z value) := by
  unfold crp_elemQ; letI := capacity.corpse; infer_instance
instance crp_elem_timeless name z value : Timeless (crp_elem capacity name z value) := by
  unfold crp_elem; infer_instance
instance region_pending_timeless name z : Timeless (region_pending capacity name z) := by
  unfold region_pending; infer_instance

theorem ticket_valid : ✓ ticketElem := trivial
theorem ticket_invalid : ¬ ✓ (ticketElem • ticketElem) := id

theorem redeem_ticketA_excl gr :
    iprop(⊢ redeem_ticketA capacity gr -∗ redeem_ticketA capacity gr -∗ False) := by
  unfold redeem_ticketA
  iintro H1 H2
  ihave %h := iOwn_cmraValid_op (E := capacity.ticket) $$ [$H1 $H2]
  exact (ticket_invalid h).elim

theorem allocate_ticket (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ gr, redeem_ticketA capacity gr ∗ frame) := by
  iintro HR
  imod iOwn_alloc (E := capacity.ticket) ticketElem ticket_valid with ⟨%gr, Ht⟩
  imodintro
  iexists gr
  unfold redeem_ticketA
  iframe Ht HR

theorem reg_agree name dq1 dq2 z (left right : RegistryValue) :
    iprop(⊢ reg_elem capacity name dq1 z left -∗ reg_elem capacity name dq2 z right -∗ ⌜left = right⌝) := by
  letI := capacity.registry
  unfold reg_elem
  iintro H1 H2
  iapply ghost_map_elem_agree (H := TokenMap) name z dq1 dq2 left right
  iframe H1 H2

theorem reg_half_agree name z ge gr ge' gr' :
    iprop(⊢ reg_half capacity name z ge gr -∗ reg_half capacity name z ge' gr' -∗ ⌜ge = ge' ∧ gr = gr'⌝) := by
  unfold reg_half
  iintro H1 H2
  ihave %h := reg_agree capacity name _ _ z (ge, gr) (ge', gr') $$ H1 H2
  ipureintro
  exact Prod.mk.inj h

theorem reg_full_half_False name z ge gr ge' gr' :
    iprop(⊢ reg_full capacity name z ge gr -∗ reg_half capacity name z ge' gr' -∗ False) := by
  letI := capacity.registry
  unfold reg_full reg_half reg_elem
  iintro H1 H2
  icases ghost_map_elem_valid_2 (H := TokenMap) name z (.own 1) (.own (1 : Qp).half)
    (ge, gr) (ge', gr') $$ [$H1 $H2] with ⟨%valid, _⟩
  exact (CMRA.not_valid_excl_op_left (x := DFrac.own 1) (y := DFrac.own (1 : Qp).half) valid).elim

theorem reg_split_iff name z ge gr :
    iprop(reg_full capacity name z ge gr ⊣⊢ reg_half capacity name z ge gr ∗ reg_half capacity name z ge gr) := by
  letI := capacity.registry
  unfold reg_full reg_half reg_elem
  have h := Fractional.fractional (Φ := fun q : Qp =>
    (ghost_map_elem name (.own q) z (ge, gr) : IProp GF)) (1 : Qp).half (1 : Qp).half
  simpa only [Qp.half_add_half] using h

theorem reg_join name z ge gr :
    iprop(⊢ reg_half capacity name z ge gr -∗ reg_half capacity name z ge gr -∗ reg_full capacity name z ge gr) := by
  iintro H1 H2
  iapply (reg_split_iff capacity name z ge gr).mpr
  iframe H1 H2

theorem reg_split name z ge gr :
    iprop(reg_full capacity name z ge gr ⊢ reg_half capacity name z ge gr ∗ reg_half capacity name z ge gr) :=
  (reg_split_iff capacity name z ge gr).mp

theorem crp_elem_agree name dq1 dq2 z (left right : Corpse) :
    iprop(⊢ crp_elemQ capacity name dq1 z left -∗ crp_elemQ capacity name dq2 z right -∗ ⌜left = right⌝) := by
  letI := capacity.corpse
  unfold crp_elemQ
  iintro H1 H2
  iapply ghost_map_elem_agree (H := TokenMap) name z dq1 dq2 left right
  iframe H1 H2

theorem crp_elem_excl name z (left right : Corpse) :
    iprop(⊢ crp_elem capacity name z left -∗ crp_elem capacity name z right -∗ False) := by
  letI := capacity.corpse
  unfold crp_elem crp_elemQ
  iintro H1 H2
  icases ghost_map_elem_valid_2 (H := TokenMap) name z (.own 1) (.own 1) left right $$ [$H1 $H2] with ⟨%valid, _⟩
  exact (CMRA.not_valid_excl_op_left (x := DFrac.own 1) (y := DFrac.own 1) valid).elim

theorem region_pending_intro name z ge gr :
    iprop(⊢ reg_half capacity name z ge gr -∗ committedA capacity ge -∗ region_pending capacity name z) := by
  unfold region_pending
  iintro Hreg Hcommitted
  iexists ge, gr
  iframe Hreg Hcommitted

theorem region_pending_open name z :
    iprop(region_pending capacity name z ⊢ ∃ ge gr,
      reg_half capacity name z ge gr ∗ committedA capacity ge) := .rfl

theorem reg_lookup name rows dq z pair :
    iprop(⊢ reg_auth capacity name rows -∗ reg_elem capacity name dq z pair -∗ ⌜rows[z]? = some pair⌝) := by
  letI := capacity.registry
  exact ghost_map_lookup

theorem reg_insert name rows z ge gr (fresh : rows[z]? = none) :
    iprop(⊢ reg_auth capacity name rows ==∗
      reg_auth capacity name (PartialMap.insert rows z (ge, gr)) ∗ reg_full capacity name z ge gr) := by
  letI := capacity.registry
  exact ghost_map_insert z (ge, gr) fresh

theorem reg_update name rows z ge gr ge' gr' :
    iprop(⊢ reg_auth capacity name rows -∗ reg_full capacity name z ge gr ==∗
      reg_auth capacity name (PartialMap.insert rows z (ge', gr')) ∗ reg_full capacity name z ge' gr') := by
  letI := capacity.registry
  exact ghost_map_update (ge', gr')

theorem reg_delete name rows z ge gr :
    iprop(⊢ reg_auth capacity name rows -∗ reg_full capacity name z ge gr ==∗
      reg_auth capacity name (PartialMap.delete rows z)) := by
  letI := capacity.registry
  exact ghost_map_delete z (ge, gr)

theorem allocate_registry (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ name, reg_auth capacity name ∅ ∗ frame) := by
  letI := capacity.registry
  iintro HR
  imod ghost_map_alloc_empty (H := TokenMap) (K := Int) (V := RegistryValue) with ⟨%name, Ha⟩
  imodintro
  iexists name
  unfold reg_auth
  iframe Ha HR

theorem crp_lookup name rows dq z value :
    iprop(⊢ crp_auth capacity name rows -∗ crp_elemQ capacity name dq z value -∗ ⌜rows[z]? = some value⌝) := by
  letI := capacity.corpse
  exact ghost_map_lookup

theorem crp_insert name rows z value (fresh : rows[z]? = none) :
    iprop(⊢ crp_auth capacity name rows ==∗
      crp_auth capacity name (PartialMap.insert rows z value) ∗ crp_elem capacity name z value) := by
  letI := capacity.corpse
  exact ghost_map_insert z value fresh

theorem crp_update name rows z old new :
    iprop(⊢ crp_auth capacity name rows -∗ crp_elem capacity name z old ==∗
      crp_auth capacity name (PartialMap.insert rows z new) ∗ crp_elem capacity name z new) := by
  letI := capacity.corpse
  exact ghost_map_update new

theorem crp_delete name rows z value :
    iprop(⊢ crp_auth capacity name rows -∗ crp_elem capacity name z value ==∗
      crp_auth capacity name (PartialMap.delete rows z)) := by
  letI := capacity.corpse
  exact ghost_map_delete z value

theorem allocate_corpses (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ name, crp_auth capacity name ∅ ∗ frame) := by
  letI := capacity.corpse
  iintro HR
  imod ghost_map_alloc_empty (H := TokenMap) (K := Int) (V := Corpse) with ⟨%name, Ha⟩
  imodintro
  iexists name
  unfold crp_auth
  iframe Ha HR

/-- Rebinding a row uses its full fragment and preserves the caller's frame. -/
theorem reg_update_frame name rows z ge gr ge' gr' (frame : IProp GF) :
    iprop(⊢ reg_auth capacity name rows -∗ (reg_full capacity name z ge gr ∗ frame) ==∗
      reg_auth capacity name (PartialMap.insert rows z (ge', gr')) ∗
      reg_full capacity name z ge' gr' ∗ frame) := by
  iintro Ha ⟨Hf, HR⟩
  imod reg_update capacity name rows z ge gr ge' gr' $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Hf HR

theorem crp_update_frame name rows z old new (frame : IProp GF) :
    iprop(⊢ crp_auth capacity name rows -∗ (crp_elem capacity name z old ∗ frame) ==∗
      crp_auth capacity name (PartialMap.insert rows z new) ∗ crp_elem capacity name z new ∗ frame) := by
  iintro Ha ⟨Hf, HR⟩
  imod crp_update capacity name rows z old new $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Hf HR

/-- Agreement retains both pre-deposit fields, including the exact positive share. -/
theorem crp_pre_agree name dq1 dq2 z t q t' q' :
    iprop(⊢ crp_elemQ capacity name dq1 z (.pre t q) -∗
      crp_elemQ capacity name dq2 z (.pre t' q') -∗ ⌜t = t' ∧ q = q'⌝) := by
  iintro H1 H2
  ihave %h := crp_elem_agree capacity name dq1 dq2 z (.pre t q) (.pre t' q') $$ H1 H2
  ipureintro
  exact Corpse.pre.inj h

/-- A supplied full row refutes the pending arm without opening an escrow. -/
theorem reg_full_pending_False name z ge gr :
    iprop(⊢ reg_full capacity name z ge gr -∗ region_pending capacity name z -∗ False) := by
  unfold region_pending
  iintro Hfull ⟨%ge', %gr', Hhalf, _⟩
  iapply reg_full_half_False capacity name z ge gr ge' gr' $$ Hfull Hhalf

theorem actual : Spec capacity := ⟨redeem_ticketA_excl capacity, crp_elem_excl capacity,
  reg_half_agree capacity, reg_full_half_False capacity, reg_split_iff capacity, region_pending_intro capacity⟩

end MachCSL.Logic.IcacheEscrowTokens
