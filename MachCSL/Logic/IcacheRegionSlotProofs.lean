import MachCSL.Logic.IcacheRegionSlotSpec
import MachCSL.Logic.IcacheInodeCustodyProofs
import MachCSL.Logic.IcacheEpochProofs
import MachCSL.Logic.IcacheEscrowTokensProofs
import MachCSL.Logic.IcacheShelterProofs
import MachCSL.Logic.FsInodeRegionProofs
import MachCSL.Logic.IcacheSlotCouplingProofs

namespace MachCSL.Logic.IcacheRegionSlot
open Iris Iris.BI Xv6.Fs IcacheRefLedger IcacheSlotCoupling

theorem ireg_in_shape (c : ClaimCell) (d : Dinode) (h : ireg_in c d) (nz : d.typeZ ≠ 0) :
    fresh_shape d := by
  rcases h with zero | ⟨shape, _⟩
  · exact (nz zero).elim
  · exact shape

theorem ireg_in_quiesce (c : ClaimCell) (d : Dinode) (none : c = none) (h : ireg_in c d) :
    d.typeZ = 0 := by
  rcases h with zero | ⟨_, present⟩
  · exact zero
  · exact (present none).elim

theorem ireg_link_ok_short (d : Dinode) (h : ireg_link_ok d) : d.nlinkZ ≤ 32767 := h.2.1
theorem ireg_link_ok_ty (d : Dinode) (h : ireg_link_ok d) : ireg_ty_ok d := h.2.2
theorem ireg_link_ok_free (d : Dinode) (h : ireg_link_ok d) (zero : d.typeZ = 0) :
    d.nlinkZ = 0 := h.1 zero

theorem ireg_ty_ok_stable (old new : Dinode) (stable : new.typeZ = 0 ∨ new.typeZ = old.typeZ)
    (h : ireg_link_ok old) : ireg_ty_ok new := by
  rcases stable with zero | same
  · exact .inl zero
  · unfold ireg_ty_ok InodeRegionImage.typeOK
    rw [same]
    exact h.2.2

variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
    (view : FsView.View GF) (records : GName)

instance arm_timeless z c d : Timeless (arm capacity names view records z c d) := by
  unfold arm; infer_instance
instance ireg_slot_timeless z d : Timeless (ireg_slot capacity names view records z d) := by
  unfold ireg_slot; infer_instance
instance topBoot_timeless z d : Timeless (topBoot capacity view z d) := by
  unfold topBoot; split <;> infer_instance
instance bootInput_timeless inum d ge gr : Timeless (bootInput capacity names view records inum d ge gr) := by
  unfold bootInput; infer_instance

theorem ireg_slot_intro z d c r f n
    (hlink : ireg_link_ok d) (hclaim : ireg_claim_ok c f d) (hfreeze : ireg_frz_ok f n d) :
    iprop(⊢ ireg_rcol capacity.reference names.reference z c r f n d -∗
      IcacheEpoch.ireg_ep capacity.epoch names.epoch z d -∗
      IcacheInodeCustody.ireg_lnk view capacity.links z d -∗
      (⌜c = none⌝ ∨ IcacheTypeGhost.ireg_open capacity.types names.boot) -∗
      IcacheCoupling.icnt_half capacity.coupling names.coupling z n -∗
      IcacheShelter.ireg_shp capacity.types capacity.transactions names.boot names.transactions c f -∗
      ireg_frzc capacity.coupling names.coupling z f -∗ arm capacity names view records z c d -∗
      ireg_slot capacity names view records z d) := by
  iintro Href Hep Hlink Hboot Hcnt Hshp Hmirror Harm
  unfold ireg_slot
  iframe Hep Hlink
  iexists r, c, f, n
  iframe Href Hboot Hcnt Hshp Hmirror Harm
  isplit
  · ipureintro; exact hlink
  · isplit
    · ipureintro; exact hclaim
    · ipureintro; exact hfreeze

theorem ireg_slot_link_ok z d :
    iprop(ireg_slot capacity names view records z d ⊢ ⌜ireg_link_ok d⌝) := by
  unfold ireg_slot
  iintro ⟨⟨%r, %c, %f, %n, _, Hlink, _⟩, _⟩
  iexact Hlink

theorem ireg_slot_root_alive d :
    iprop(ireg_slot capacity names view records 1 d ⊢ ⌜1 ≤ d.nlinkZ⌝) := by
  unfold ireg_slot
  iintro ⟨_, _, Hlink⟩
  iapply IcacheInodeCustody.ireg_lnk_root_alive view capacity.links d $$ Hlink

/-- A held full record rules out both arms that retain that record inside.
The source marker and full registry row remain available with the held record. -/
theorem arm_record_out z c d (held : Dinode) :
    iprop(⊢ arm capacity names view records z c d -∗ FsInodeRegion.frag capacity.records records z held -∗
      ⌜ireg_marked_ok c d⌝ ∗ FsInodeRegion.imark capacity.records records z ∗
      (∃ ge gr, IcacheEscrowTokens.reg_full capacity.escrow names.registry z ge gr) ∗
      FsInodeRegion.frag capacity.records records z held) := by
  unfold arm
  iintro Harm Hheld
  icases Harm with (⟨Hbranch, Hreg⟩ | ⟨_, Hinside, _⟩)
  · icases Hbranch with (⟨_, Hinside, _⟩ | ⟨Hmarked, Hmarker⟩)
    · ihave Hfalse := FsInodeRegion.frag_exclusive capacity.records records z d held $$ [$Hinside $Hheld]
      icases Hfalse with ⟨⟩
    · iframe Hmarked Hmarker Hreg Hheld
  · ihave Hfalse := FsInodeRegion.frag_exclusive capacity.records records z d held $$ [$Hinside $Hheld]
    icases Hfalse with ⟨⟩

theorem topBoot_live z d (h : d.typeZ ≠ 0) : iprop(⊢ topBoot capacity view z d) := by
  unfold topBoot
  rw [if_neg h]
  exact .rfl

end MachCSL.Logic.IcacheRegionSlot
