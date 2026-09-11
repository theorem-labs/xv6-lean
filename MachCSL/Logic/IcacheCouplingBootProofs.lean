import MachCSL.Logic.IcacheCouplingProofs

namespace MachCSL.Logic.IcacheCoupling
open Iris Iris.Std Iris.CMRA Iris.BI
set_option maxRecDepth 4096

theorem count_boot_valid (inums : Inums) : ✓ countBootMap inums := by
  intro i
  change ✓ (get? (M := InumMap) (FiniteMap.ofSet _ inums) i)
  by_cases member : i ∈ inums
  · rw [LawfulFiniteMap.get?_ofSet_of_mem member]
    exact DFracAgree.mk_valid.mpr DFrac.valid_own_one
  · rw [LawfulFiniteMap.get?_ofSet_of_not_mem member]
    trivial

theorem mirror_boot_valid (inums : Inums) : ✓ mirrorBootMap inums := by
  intro i
  change ✓ (get? (M := InumMap) (FiniteMap.ofSet _ inums) i)
  by_cases member : i ∈ inums
  · rw [LawfulFiniteMap.get?_ofSet_of_mem member]
    exact DFracAgree.mk_valid.mpr DFrac.valid_own_one
  · rw [LawfulFiniteMap.get?_ofSet_of_not_mem member]
    trivial

private theorem pin_list_absent (slots : List Nat) k (absent : k ∉ slots) :
    get? (M := SlotMap) (slots.foldr (fun k rest => pinElem k 1 none • rest) UCMRA.unit) k = none := by
  induction slots with
  | nil => rfl
  | cons j slots ih =>
    rw [List.foldr_cons, Heap.get?_op (M := SlotMap), ih (fun h => absent (by simp [h]))]
    have different : j ≠ k := by intro same; subst j; exact absent (by simp)
    have empty : get? (M := SlotMap) (pinElem j 1 none) k = none := LawfulPartialMap.get?_singleton_ne different
    rw [empty]
    rfl

private theorem pin_list_valid (slots : List Nat) (nodup : slots.Nodup) :
    ✓ slots.foldr (fun k rest => pinElem k 1 none • rest) (UCMRA.unit : PinRA) := by
  induction slots with
  | nil => exact UCMRA.unit_valid
  | cons k slots ih =>
    have hn := List.nodup_cons.mp nodup
    rw [List.foldr_cons]
    change ✓ (PartialMap.singleton (M := SlotMap) k (DFracAgree.Frac.mk 1 (⟨none⟩ : DiscreteO PinValue)) •
      slots.foldr (fun k rest => pinElem k 1 none • rest) UCMRA.unit)
    rw [← Heap.insert_eq_singleton_op_singleton (M := SlotMap) (pin_list_absent slots k hn.1)]
    apply Heap.insert_valid (M := SlotMap)
    · exact DFracAgree.mk_valid.mpr DFrac.valid_own_one
    · exact ih hn.2

theorem pin_boot_valid : ✓ pinBootMap := pin_list_valid (List.range 50) List.nodup_range

variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)

theorem icnt_boot_split inums : countMapOwned capacity names inums ⊢ bootCounts capacity names inums := by
  unfold countMapOwned countBootMap bootCounts
  induction inums using FiniteSet.set_ind with
  | hemp =>
    rw [BigSepS.bigSepS_empty.to_eq]
    exact affine
  | hadd i inums absent ih =>
    rw [LawfulFiniteMap.ofSet_insert,
      Heap.insert_eq_singleton_op_singleton (M := InumMap) (LawfulFiniteMap.get?_ofSet_of_not_mem absent),
      (iOwn_op (E := capacity.count)).to_eq, (BigSepS.bigSepS_insert absent).to_eq]
    exact sep_mono (count_split capacity names i 0).mp ih

theorem frzm_boot_split inums : mirrorMapOwned capacity names inums ⊢ bootMirrors capacity names inums := by
  unfold mirrorMapOwned mirrorBootMap bootMirrors
  induction inums using FiniteSet.set_ind with
  | hemp =>
    rw [BigSepS.bigSepS_empty.to_eq]
    exact affine
  | hadd i inums absent ih =>
    rw [LawfulFiniteMap.ofSet_insert,
      Heap.insert_eq_singleton_op_singleton (M := InumMap) (LawfulFiniteMap.get?_ofSet_of_not_mem absent),
      (iOwn_op (E := capacity.mirror)).to_eq, (BigSepS.bigSepS_insert absent).to_eq]
    exact sep_mono (mirror_split capacity names i false).mp ih

theorem hpn_boot_split : pinMapOwned capacity names ⊢ bootPins capacity names := by
  unfold pinMapOwned pinBootMap bootPins hpn_full hpn_at
  have split (slots : List Nat) :
      iOwn (E := capacity.pin) names.pin (slots.foldr (fun k rest => pinElem k 1 none • rest) UCMRA.unit) ⊢
      bigSepL (fun _ k => iOwn (E := capacity.pin) names.pin (pinElem k 1 none)) slots := by
    induction slots with
    | nil => exact affine
    | cons k slots ih =>
      rw [List.foldr_cons, (iOwn_op (E := capacity.pin)).to_eq, BigSepL.bigSepL_cons.to_eq]
      exact sep_mono_right ih
  exact split (List.range 50)

theorem hpn_boot_halves : bootPins capacity names ⊢
    bigSepL (fun _ k => iprop(hpn_h capacity names k none ∗ hpn_h capacity names k none)) (List.range 50) := by
  unfold bootPins
  exact BigSepL.bigSepL_mono_of_forall (pin_split capacity names _ _).mp

theorem allocate (inums : Inums) (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ names, bootCounts capacity names inums ∗ bootMirrors capacity names inums ∗ bootPins capacity names ∗ frame) := by
  iintro HR
  imod iOwn_alloc (E := capacity.count) (countBootMap inums) (count_boot_valid inums) with ⟨%gc, Hc⟩
  imod iOwn_alloc (E := capacity.mirror) (mirrorBootMap inums) (mirror_boot_valid inums) with ⟨%gm, Hm⟩
  imod iOwn_alloc (E := capacity.pin) pinBootMap pin_boot_valid with ⟨%gp, Hp⟩
  let names : Names := ⟨gc, gm, gp⟩
  have countLaw : iprop(iOwn (E := capacity.count) gc (countBootMap inums) ⊢ bootCounts capacity names inums) :=
    icnt_boot_split capacity names inums
  have mirrorLaw : iprop(iOwn (E := capacity.mirror) gm (mirrorBootMap inums) ⊢ bootMirrors capacity names inums) :=
    frzm_boot_split capacity names inums
  have pinLaw : iprop(iOwn (E := capacity.pin) gp pinBootMap ⊢ bootPins capacity names) := hpn_boot_split capacity names
  ihave Hcounts := countLaw $$ Hc
  ihave Hmirrors := mirrorLaw $$ Hm
  ihave Hpins := pinLaw $$ Hp
  imodintro
  iexists names
  iframe Hcounts Hmirrors Hpins HR

theorem actual : Spec capacity where
  countAgree := count_agree capacity
  countUpdate := count_update capacity
  mirrorAgree := mirror_agree capacity
  mirrorUpdate := mirror_update capacity
  pinAgree := pin_agree capacity
  pinUpdate := pin_full_update capacity
  countBoot := icnt_boot_split capacity
  mirrorBoot := frzm_boot_split capacity
  pinBoot := hpn_boot_split capacity
  allocate := allocate capacity

end MachCSL.Logic.IcacheCoupling
