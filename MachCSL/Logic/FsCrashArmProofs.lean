import MachCSL.Logic.FsCrashHistoryProofs

namespace MachCSL.Logic.FsCrash
open Iris Iris.Std Iris.Algebra Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance custody_timeless names covered start disk generation : Timeless (custody capacity names covered start disk generation) := by
  unfold custody; infer_instance
instance armBranch_timeless names covered start disk count : Timeless (armBranch capacity names covered start disk count) := by
  unfold armBranch; infer_instance
instance arm_timeless names covered start disk : Timeless (arm capacity names covered start disk) := by
  unfold arm; infer_instance

theorem arm_at_rest names covered start disk :
    counterAuth capacity names.swap 0 ⊢ arm capacity names covered start disk := by
  unfold arm armBranch
  iintro Ha
  iexists 0
  iframe Ha
  ileft
  ipureintro; rfl

theorem custody_started names covered start disk generation :
    custody capacity names covered start disk generation ⊢
      started capacity names generation ∗ custody capacity names covered start disk generation := by
  unfold custody
  iintro ⟨%era, %mirror, #Hr, #Hs, Hm, %ok⟩
  iframe Hs
  iexists era, mirror
  iframe Hr Hm
  ipureintro; exact ok

theorem arm_upper_bound names covered start disk generation n count (atGeneration : n = generation + 1) :
    counterAuth capacity names.started n ∗ armBranch capacity names covered start disk count ⊢
      ⌜count ≤ generation + 1⌝ ∗ counterAuth capacity names.started n ∗ armBranch capacity names covered start disk count := by
  iintro ⟨Ha, Hb⟩
  iunfold armBranch at Hb
  icases Hb with (%zero | Hcust)
  · iframe Ha
    isplit
    · ipureintro; omega
    · unfold armBranch
      ileft; ipureintro; exact zero
  · icases Hcust with ⟨%g, %same, Hcust⟩
    ihave ⟨#Hs, Hcust⟩ := custody_started capacity names covered start disk g $$ Hcust
    iunfold started at Hs
    ihave %bound := counter_valid capacity names.started n (g + 1) $$ [$Ha $Hs]
    iframe Ha
    isplit
    · ipureintro; omega
    · unfold armBranch
      iright
      iexists g
      iframe Hcust
      ipureintro; exact same

theorem arm_swap names covered start disk next generation era n mirror
    (atGeneration : n = generation + 1) (ok : MirrorOK mirror (Xv6.Fs.blocks next) covered start) :
    iprop(⊢ registered capacity names generation era -∗ started capacity names generation -∗
      counterAuth capacity names.started n -∗ mirrorHalf capacity era.logMirror mirror -∗
      arm capacity names covered start disk ==∗ arm capacity names covered start next ∗
      counterAuth capacity names.started n ∗ counterLowerBound capacity names.swap (generation + 1)) := by
  iintro #Hr #Hs Hsa Hm Harm
  iunfold arm at Harm
  icases Harm with ⟨%count, Hc, Hb⟩
  ihave ⟨%upper, Hsa, _⟩ := arm_upper_bound capacity names covered start disk generation n count
    atGeneration $$ [$Hsa $Hb]
  imod counter_update capacity names.swap count (generation + 1) upper $$ Hc with ⟨Hc, #Hlb⟩
  imodintro
  iframe Hsa Hlb
  unfold arm armBranch
  iexists (generation + 1)
  iframe Hc
  iright
  iexists generation
  isplit
  · ipureintro; rfl
  · unfold custody
    iexists era, mirror
    iframe Hr Hs Hm
    ipureintro; exact ok

theorem registered_agree names generation left right :
    registered capacity names generation left ∗ registered capacity names generation right ⊢ ⌜left = right⌝ := by
  unfold registered Era.registered
  letI := capacity.registry.entries
  iintro H
  iapply ghost_map_elem_agree $$ H

theorem mirror_agree name left right : mirrorHalf capacity name left ∗ mirrorHalf capacity name right ⊢ ⌜left = right⌝ := by
  unfold mirrorHalf
  letI := capacity.mirror
  iintro ⟨Hl, Hr⟩
  iapply ghost_var_agree $$ Hl Hr

theorem mirror_update name left right next :
    iprop(⊢ mirrorHalf capacity name left -∗ mirrorHalf capacity name right ==∗
      mirrorHalf capacity name next ∗ mirrorHalf capacity name next) := by
  unfold mirrorHalf
  letI := capacity.mirror
  exact ghost_var_update_halves next name left right

theorem arm_accessor names covered start disk generation era n mirror
    (atGeneration : n = generation + 1) :
    iprop(⊢ registered capacity names generation era -∗ counterLowerBound capacity names.swap (generation + 1) -∗
      counterAuth capacity names.started n -∗ mirrorHalf capacity era.logMirror mirror -∗
      arm capacity names covered start disk -∗
      ⌜MirrorOK mirror (Xv6.Fs.blocks disk) covered start⌝ ∗ counterAuth capacity names.started n ∗
      (∀ (next : Physical) (newMirror : LogMirror),
        ⌜MirrorOK newMirror (Xv6.Fs.blocks next) covered start⌝ ==∗
        arm capacity names covered start next ∗ mirrorHalf capacity era.logMirror newMirror)) := by
  iintro #Hr #Hlb Hsa Hm Harm
  iunfold arm at Harm
  icases Harm with ⟨%count, Hc, Hb⟩
  ihave ⟨%upper, Hsa, Hb⟩ := arm_upper_bound capacity names covered start disk generation n count
    atGeneration $$ [$Hsa $Hb]
  ihave %lower := counter_valid capacity names.swap count (generation + 1) $$ [$Hc $Hlb]
  iunfold armBranch at Hb
  icases Hb with (%zero | Hcust)
  · exfalso; omega
  · icases Hcust with ⟨%g, %sameCount, Hcust⟩
    have sameGeneration : g = generation := by omega
    subst g
    iunfold custody at Hcust
    icases Hcust with ⟨%otherEra, %otherMirror, #Hr2, #Hs2, Hm2, %ok⟩
    ihave %sameEra := registered_agree capacity names generation era otherEra $$ [$Hr $Hr2]
    subst otherEra
    ihave %sameMirror := mirror_agree capacity era.logMirror mirror otherMirror $$ [$Hm $Hm2]
    subst otherMirror
    iframe Hsa
    isplit
    · ipureintro; exact ok
    · iintro %next %newMirror %nextOK
      imod mirror_update capacity era.logMirror mirror mirror newMirror $$ Hm Hm2 with ⟨Hm, Hm2⟩
      imodintro
      iframe Hm
      unfold arm armBranch
      iexists count
      iframe Hc
      iright
      iexists generation
      isplit
      · ipureintro; exact sameCount
      · unfold custody
        iexists era, newMirror
        iframe Hr Hs2 Hm2
        ipureintro; exact nextOK

theorem armSpec : ArmSpec capacity :=
  ⟨arm_at_rest capacity, custody_started capacity, arm_upper_bound capacity, arm_swap capacity, arm_accessor capacity⟩

end MachCSL.Logic.FsCrash
