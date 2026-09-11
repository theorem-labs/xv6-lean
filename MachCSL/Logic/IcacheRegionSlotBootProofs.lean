import MachCSL.Logic.IcacheRegionSlotProofs

namespace MachCSL.Logic.IcacheRegionSlot
open Iris Iris.BI Xv6.Fs IcacheRefLedger IcacheSlotCoupling
variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
    (view : FsView.View GF) (records : GName)

/-- Pointwise source boot routing from supplied components, retaining the
outside record/marker and arbitrary caller frame. No ghost name is allocated. -/
theorem boot_slot (inum : BitVec 32) d ge gr (frame : IProp GF)
    (hlink : ireg_link_ok d) (hbare : d.typeZ = 0 → IcacheInodeCustody.ireg_bare d) :
    iprop(bootInput capacity names view records inum d ge gr ∗ frame ⊢ |==>
      (ireg_slot capacity names view records inum.toNat d ∗ FsInodeRegion.out capacity.records records inum d ∗ frame)) := by
  unfold bootInput
  iintro ⟨⟨Hrecord, Hmarker, Href, Hobs, Hreg, Hcount, Hmirror, Hlink, Htop⟩, HR⟩
  imod IcacheEpoch.ireg_ep_intro capacity.epoch names.epoch (inum.toNat : Int) d $$ Hobs with Hep
  ihave Href := ireg_rcol_intro capacity.reference names.reference (inum.toNat : Int)
    none 0 (freezeCell .off) 0 0 d (ireg_ref_ok_zero 0 none d) $$ Href
  ihave Hmirror := ireg_frzc_off_intro capacity.coupling names.coupling (inum.toNat : Int)
    (freezeCell .off) rfl $$ Hmirror
  have shelter : iprop(⊢ IcacheShelter.ireg_shp capacity.types capacity.transactions names.boot
      names.transactions none (freezeCell .off)) :=
    (IcacheShelter.ireg_fsh_off capacity.types capacity.transactions names.boot names.transactions).trans
      (IcacheShelter.ireg_shp_none capacity.types capacity.transactions names.boot names.transactions (freezeCell .off))
  ihave Hshp := shelter
  have boot : iprop(⊢ ⌜(none : ClaimCell) = none⌝ ∨ IcacheTypeGhost.ireg_open capacity.types names.boot) := by
    ileft; ipureintro; rfl
  ihave Hboot := boot
  imodintro
  by_cases free : d.typeZ = 0
  · rw [FsInodeRegion.out_free capacity.records records inum d free]
    isplitl [Hrecord Href Hep Hreg Hcount Hmirror Hlink Htop Hshp Hboot]
    · iapply ireg_slot_intro capacity names view records (inum.toNat : Int) d none 0 (freezeCell .off) 0
        hlink (ireg_claim_ok_none _ _) True.intro $$ Href Hep Hlink Hboot Hcount Hshp Hmirror
      unfold arm
      ileft
      isplitl [Hrecord Htop]
      · ileft
        isplitr [Hrecord Htop]
        · ipureintro; exact .inl free
        · iunfold FsInodeRegion.dinodeAt at Hrecord
          iframe Hrecord
          have top : topBoot capacity view (inum.toNat : Int) d =
              FsTop.topFrag capacity.tops view (inum.toNat : Int) (IcacheInodeCustody.freeNode d) := by
            simp only [topBoot, free, ↓reduceIte]
          isimp only [top] at Htop
          iapply IcacheInodeCustody.ireg_top_park_free view capacity.tops (inum.toNat : Int) d (hbare free) $$ Htop
      · iexists ge, gr
        iexact Hreg
    · iframe Hmarker HR
  · rw [FsInodeRegion.out_allocated capacity.records records inum d free]
    isplitl [Hmarker Href Hep Hreg Hcount Hmirror Hlink Hshp Hboot]
    · iapply ireg_slot_intro capacity names view records (inum.toNat : Int) d none 0 (freezeCell .off) 0
        hlink (ireg_claim_ok_none _ _) True.intro $$ Href Hep Hlink Hboot Hcount Hshp Hmirror
      unfold arm
      ileft
      isplitl [Hmarker]
      · iright
        iframe Hmarker
        ipureintro; exact ⟨free, rfl⟩
      · iexists ge, gr
        iexact Hreg
    · iframe Hrecord HR

theorem actual : Spec capacity where
  intro := fun names view records z d c r f n => ireg_slot_intro capacity names view records z d c r f n
  boot := fun names view records inum d ge gr frame => boot_slot capacity names view records inum d ge gr frame

end MachCSL.Logic.IcacheRegionSlot
