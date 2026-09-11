import MachCSL.Logic.IcacheRefLedgerUpdateProofs

namespace MachCSL.Logic.IcacheRefLedger
open Iris Iris.Std Iris.CMRA Iris.BI
open scoped CommMonoidLike

theorem lelem_boot_valid : ✓ lelem_boot := by repeat constructor

theorem boot_element_valid : ✓ ((● lelem_boot : Auth Element) • ◯ lelem_boot) :=
  Auth.auth_both_valid_discrete.mpr ⟨⟨UCMRA.unit, CMRA.unit_right_id.symm⟩, lelem_boot_valid⟩

theorem boot_map_valid (inums : _root_.Std.ExtTreeSet Int) : ✓ bootMap inums := by
  intro i
  change ✓ (get? (M := LedgerMap) (FiniteMap.ofSet _ inums) i)
  by_cases member : i ∈ inums
  · rw [LawfulFiniteMap.get?_ofSet_of_mem member]
    exact boot_element_valid
  · rw [LawfulFiniteMap.get?_ofSet_of_not_mem member]
    trivial

theorem boot_map_lookup (inums : _root_.Std.ExtTreeSet Int) (i : Int) :
    (bootMap inums)[i]? = if i ∈ inums then some ((● lelem_boot : Auth Element) • ◯ lelem_boot) else none := by
  change get? (M := LedgerMap) (FiniteMap.ofSet _ inums) i = _
  split
  · exact LawfulFiniteMap.get?_ofSet_of_mem ‹_›
  · exact LawfulFiniteMap.get?_ofSet_of_not_mem ‹_›

variable {GF : BundledGFunctors} (capacity : Capacity GF) (g : GName)

theorem boot_cell i :
    iOwn (E := capacity.ledger) g (PartialMap.singleton (M := LedgerMap) i ((● lelem_boot : Auth Element) • ◯ lelem_boot)) ⊣⊢
    link_auth capacity g i none 0 (freezeCell .off) 0 ∗ ifreeze_off capacity g i := by
  unfold link_auth link_auth_e ifreeze_off ifreeze link_frag_e authElem fragElem
  rw [← Heap.singleton_op_singleton (M := LedgerMap)]
  exact iOwn_op (E := capacity.ledger)

theorem link_boot_split inums : bootOwned capacity g inums ⊢ bootRows capacity g inums := by
  unfold bootOwned bootMap bootRows
  induction inums using FiniteSet.set_ind with
  | hemp => rw [BigSepS.bigSepS_empty.to_eq]; exact affine
  | hadd i inums absent ih =>
    rw [LawfulFiniteMap.ofSet_insert,
      Heap.insert_eq_singleton_op_singleton (M := LedgerMap) (LawfulFiniteMap.get?_ofSet_of_not_mem absent),
      (iOwn_op (E := capacity.ledger)).to_eq, (BigSepS.bigSepS_insert absent).to_eq]
    exact sep_mono (boot_cell capacity g i).mp ih

theorem allocate inums (frame : IProp GF) : iprop(frame ⊢ |==> ∃ g, bootRows capacity g inums ∗ frame) := by
  iintro HR
  imod iOwn_alloc (E := capacity.ledger) (bootMap inums) (boot_map_valid inums) with ⟨%name, H⟩
  have split : iprop(iOwn (E := capacity.ledger) name (bootMap inums) ⊢ bootRows capacity name inums) :=
    link_boot_split capacity name inums
  ihave Hrows := split $$ H
  imodintro
  iexists name
  iframe Hrows HR

theorem actual : Spec capacity where
  claimAgree := link_claim_agree capacity
  freezeAgree := link_freeze_agree capacity
  freezeExclusive := ifreeze_excl capacity
  claimMint := link_mint_claim capacity
  claimSpend := link_spend_claim capacity
  refMint := link_mint_runit capacity
  refSpend := link_spend_runit capacity
  freezeStep := link_freeze_step capacity
  boot := link_boot_split capacity
  allocate := allocate capacity

end MachCSL.Logic.IcacheRefLedger
