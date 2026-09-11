import MachCSL.Logic.FsViewSpec

namespace MachCSL.Logic.FsView
open Iris Iris.Std Iris.CMRA Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors} (view : View GF)

instance byteRangeQ_timeless [GTimeless view] dq b off bytes :
    Timeless (byteRangeQ view dq b off bytes) := by unfold byteRangeQ; infer_instance
instance byteRange_timeless [GTimeless view] b off bytes :
    Timeless (byteRange view b off bytes) := by unfold byteRange; infer_instance
instance blockOwnedQ_timeless [GTimeless view] dq b bytes :
    Timeless (blockOwnedQ view dq b bytes) := by unfold blockOwnedQ; infer_instance
instance blockOwned_timeless [GTimeless view] b bytes :
    Timeless (blockOwned view b bytes) := by unfold blockOwned; infer_instance

theorem byteRange_one b off bytes : byteRange view b off bytes = byteRangeQ view (.own 1) b off bytes := rfl
theorem blockOwned_one b bytes : blockOwned view b bytes = blockOwnedQ view (.own 1) b bytes := rfl

theorem blockOwnedQ_length dq b bytes : blockOwnedQ view dq b bytes ⊢ ⌜bytes.length = 1024⌝ := by
  unfold blockOwnedQ
  iintro ⟨%length, _⟩
  ipureintro
  exact length
theorem blockOwned_length b bytes : blockOwned view b bytes ⊢ ⌜bytes.length = 1024⌝ :=
  blockOwnedQ_length view (.own 1) b bytes

theorem byteRangeQ_nil dq b off : byteRangeQ view dq b off [] ⊣⊢ emp := .rfl
theorem byteRange_nil b off : byteRange view b off [] ⊣⊢ emp := .rfl

theorem byteRangeQ_append dq b off left right :
    byteRangeQ view dq b off (left ++ right) ⊣⊢
      byteRangeQ view dq b off left ∗ byteRangeQ view dq b (off + (left.length : Int)) right := by
  unfold byteRangeQ
  rw [BigSepL.bigSepL_append.to_eq]
  have same : (fun (k : Nat) (v : Byte) => view.phi dq (b * 1024 + off + ((k + left.length : Nat) : Int)) v) =
      (fun (k : Nat) v => view.phi dq (b * 1024 + (off + (left.length : Int)) + (k : Int)) v) := by
    funext k v
    congr 1
    omega
  rw [same]
  exact .rfl

theorem byteRange_append b off left right :
    byteRange view b off (left ++ right) ⊣⊢
      byteRange view b off left ∗ byteRange view b (off + (left.length : Int)) right :=
  byteRangeQ_append view (.own 1) b off left right

theorem byteRangeQ_split (fractional : PhiFrac view) q1 q2 b off bytes :
    byteRangeQ view (.own (q1 + q2)) b off bytes ⊣⊢
      byteRangeQ view (.own q1) b off bytes ∗ byteRangeQ view (.own q2) b off bytes := by
  unfold byteRangeQ
  rw [← BigSepL.bigSepL_sep_eqv.to_eq]
  apply BIBase.BiEntails.of_eq
  congr 1
  funext k v
  exact (fractional _ v q1 q2).to_eq

theorem blockOwnedQ_split (fractional : PhiFrac view) q1 q2 b bytes :
    blockOwnedQ view (.own (q1 + q2)) b bytes ⊣⊢
      blockOwnedQ view (.own q1) b bytes ∗ blockOwnedQ view (.own q2) b bytes := by
  unfold blockOwnedQ
  rw [(byteRangeQ_split view fractional q1 q2 b 0 bytes).to_eq]
  constructor
  · iintro ⟨%length, Hl, Hr⟩
    isplitl [Hl]
    · iframe Hl
      ipureintro
      exact length
    · iframe Hr
      ipureintro
      exact length
  · iintro ⟨⟨%length, Hl⟩, ⟨_, Hr⟩⟩
    iframe Hl Hr
    ipureintro
    exact length

theorem threeQuarters_quarter : Qp.threeQuarters + Qp.quarter = 1 := by
  apply Subtype.ext
  change (3 / 4 : Rat) + 1 / 4 = 1
  grind

theorem blockOwned_split34 (fractional : PhiFrac view) b bytes :
    blockOwned view b bytes ⊣⊢ blockOwnedQ view (.own Qp.threeQuarters) b bytes ∗
      blockOwnedQ view (.own Qp.quarter) b bytes := by
  rw [blockOwned_one, ← threeQuarters_quarter]
  exact blockOwnedQ_split view fractional _ _ _ _

theorem gammaQ_byteRange dq b off bytes :
    byteRange (gammaQ view dq) b off bytes = byteRangeQ view dq b off bytes := rfl
theorem gammaQ_blockOwned dq b bytes :
    blockOwned (gammaQ view dq) b bytes = blockOwnedQ view dq b bytes := rfl
theorem gammaQ_one_byteRange b off bytes :
    byteRange (gammaQ view (.own 1)) b off bytes = byteRange view b off bytes := rfl
theorem gammaQ_one_blockOwned b bytes :
    blockOwned (gammaQ view (.own 1)) b bytes = blockOwned view b bytes := rfl
theorem gammaQ_names dq : (gammaQ view dq).link = view.link ∧ (gammaQ view dq).top = view.top := ⟨rfl, rfl⟩

instance gammaQ_timeless [GTimeless view] dq : GTimeless (gammaQ view dq) where
  timeless _ a v := GTimeless.timeless dq a v

theorem gammaQ_shed (fractional : PhiFrac view) q1 q2 :
    ViewShed (gammaQ view (.own (q1 + q2))) (gammaQ view (.own q1)) (gammaQ view (.own q2)) :=
  fun a v => (fractional a v q1 q2).mp

theorem gamma_shed_full (fractional : PhiFrac view) q1 q2 (sum : q1 + q2 = 1) :
    ViewShed view (gammaQ view (.own q1)) (gammaQ view (.own q2)) := by
  intro a v
  change view.phi (.own 1) a v ⊢ _
  rw [← sum]
  exact (fractional a v q1 q2).mp

theorem gamma_shed34 (fractional : PhiFrac view) :
    ViewShed view (gammaQ view (.own Qp.threeQuarters)) (gammaQ view (.own Qp.quarter)) :=
  gamma_shed_full view fractional _ _ threeQuarters_quarter

theorem byteRange_shed (left right : View GF) (shed : ViewShed view left right) b off bytes :
    byteRange view b off bytes ⊢ byteRange left b off bytes ∗ byteRange right b off bytes := by
  unfold byteRange byteRangeQ
  rw [← BigSepL.bigSepL_sep_eqv.to_eq]
  exact BigSepL.bigSepL_mono_of_forall (shed _ _)

theorem blockOwned_shed (left right : View GF) (shed : ViewShed view left right) b bytes :
    blockOwned view b bytes ⊢ blockOwned left b bytes ∗ blockOwned right b bytes := by
  unfold blockOwned
  iintro ⟨%length, Hb⟩
  ihave ⟨Hl, Hr⟩ := byteRange_shed view left right shed b 0 bytes $$ Hb
  isplitl [Hl]
  · iframe Hl
    ipureintro
    exact length
  · iframe Hr
    ipureintro
    exact length

theorem byteRangeQ_valid (exclusive : PhiExcl view) dq1 dq2 b off bytes other
    (nonempty : 0 < bytes.length) (nonempty' : 0 < other.length) :
    iprop(⊢ byteRangeQ view dq1 b off bytes -∗ byteRangeQ view dq2 b off other -∗ ⌜✓ (dq1 • dq2)⌝) := by
  unfold byteRangeQ
  iintro Hl Hr
  ihave H1 := BigSepL.bigSepL_lookup (List.getElem?_eq_getElem nonempty) $$ Hl
  ihave H2 := BigSepL.bigSepL_lookup (List.getElem?_eq_getElem nonempty') $$ Hr
  iapply exclusive _ _ _ dq1 dq2
  iframe H1 H2

theorem byteRangeQ_excl (exclusive : PhiExcl view) (dq1 dq2 : DFrac) b off bytes other
    (invalid : ¬ ✓ (dq1 • dq2)) (nonempty : 0 < bytes.length) (nonempty' : 0 < other.length) :
    iprop(⊢ byteRangeQ view dq1 b off bytes -∗ byteRangeQ view dq2 b off other -∗ False) := by
  iintro Hl Hr
  ihave %valid := byteRangeQ_valid view exclusive dq1 dq2 b off bytes other nonempty nonempty' $$ Hl Hr
  ipureintro
  exact invalid valid

theorem dfrac_full_invalid (dq : DFrac) : ¬ ✓ (DFrac.own 1 • dq) := by
  intro valid
  have h := DFrac.valid_own_op valid
  change (1 : Rat) < 1 at h
  exact (Rat.lt_irrefl h)

theorem dfrac_threeQuarters_invalid : ¬ ✓ (DFrac.own Qp.threeQuarters • DFrac.own Qp.threeQuarters) := by
  change ¬ ((3 / 4 : Rat) + 3 / 4 ≤ 1)
  grind

theorem byteRange_excl (exclusive : PhiExcl view) b off bytes other
    (nonempty : 0 < bytes.length) (nonempty' : 0 < other.length) :
    iprop(⊢ byteRange view b off bytes -∗ byteRange view b off other -∗ False) :=
  byteRangeQ_excl view exclusive _ _ b off bytes other (dfrac_full_invalid _) nonempty nonempty'

theorem blockOwnedQ_excl (exclusive : PhiExcl view) (dq1 dq2 : DFrac) b bytes other
    (invalid : ¬ ✓ (dq1 • dq2)) :
    iprop(⊢ blockOwnedQ view dq1 b bytes -∗ blockOwnedQ view dq2 b other -∗ False) := by
  unfold blockOwnedQ
  iintro ⟨%length, Hl⟩ ⟨%length', Hr⟩
  iapply byteRangeQ_excl view exclusive dq1 dq2 b 0 bytes other invalid (by omega) (by omega) $$ Hl Hr

theorem blockOwned_excl (exclusive : PhiExcl view) b bytes other :
    iprop(⊢ blockOwned view b bytes -∗ blockOwned view b other -∗ False) :=
  blockOwnedQ_excl view exclusive _ _ b bytes other (dfrac_full_invalid _)

theorem blockOwnedQ_ne (exclusive : PhiExcl view) (dq1 dq2 : DFrac) b b' bytes other
    (invalid : ¬ ✓ (dq1 • dq2)) :
    iprop(⊢ blockOwnedQ view dq1 b bytes -∗ blockOwnedQ view dq2 b' other -∗ ⌜b ≠ b'⌝) := by
  iintro Hl Hr
  by_cases same : b = b'
  · subst b'
    ihave Hfalse := blockOwnedQ_excl view exclusive dq1 dq2 b bytes other invalid $$ Hl Hr
    icases Hfalse with ⟨⟩
  · ipureintro
    exact same

theorem blockOwned_ne (exclusive : PhiExcl view) b b' bytes other :
    iprop(⊢ blockOwned view b bytes -∗ blockOwned view b' other -∗ ⌜b ≠ b'⌝) :=
  blockOwnedQ_ne view exclusive _ _ b b' bytes other (dfrac_full_invalid _)

theorem blockOwned_ne_full (exclusive : PhiExcl view) dq b b' bytes other :
    iprop(⊢ blockOwned view b bytes -∗ blockOwnedQ view dq b' other -∗ ⌜b ≠ b'⌝) :=
  blockOwnedQ_ne view exclusive _ _ b b' bytes other (dfrac_full_invalid _)

theorem blockOwned_ne34 (exclusive : PhiExcl view) b b' bytes other :
    iprop(⊢ blockOwnedQ view (.own Qp.threeQuarters) b bytes -∗
      blockOwnedQ view (.own Qp.threeQuarters) b' other -∗ ⌜b ≠ b'⌝) :=
  blockOwnedQ_ne view exclusive _ _ b b' bytes other dfrac_threeQuarters_invalid

end MachCSL.Logic.FsView
