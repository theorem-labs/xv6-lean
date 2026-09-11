import MachCSL.Logic.IcacheRegionBootDistributionProofs

namespace MachCSL.Logic.IcacheRegionBoot
open Iris Iris.Std Iris.BI Xv6.Fs SnapshotConfig
variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names) (view : FsView.View GF)

/-- Source's six independent set columns, regrouped without allocation. -/
theorem clients_columns nib counts imageRecords : clients capacity names view nib counts imageRecords ⊣⊢
    iprop((bigSepS (fun z => IcacheRefLedger.link_auth capacity.reference names.reference z none 0
      (IcacheRefLedger.freezeCell .off) 0) (regionInums nib)) ∗
    (bigSepS (fun z => LogEpoch.epochAuth capacity.epoch (names.epoch.observation z) 0) (regionInums nib)) ∗
    (bigSepS (fun z => IcacheCoupling.icnt_half capacity.coupling names.coupling z 0) (regionInums nib)) ∗
    (bigSepS (fun z => IcacheCoupling.frzm_h capacity.coupling names.coupling z false) (regionInums nib)) ∗
    (bigSepS (fun z => IcacheInodeCustody.ireg_lnk_at view capacity.links z (counts z) (imageRecords z).typeZ) (regionInums nib)) ∗
    bigSepS (fun z => IcacheRegionSlot.topBoot capacity view z (imageRecords z)) (regionInums nib)) := by
  unfold clients
  repeat rw [BigSepS.bigSepS_sep.to_eq]
  exact .rfl

theorem slots_from_clients records dss (nib : Nat) counts imageRecords
    (bound : 16 * (nib : Int) ≤ 2 ^ 32)
    (checks : InodeRegionImage.Premises dss nib counts imageRecords) :
    iprop(⊢ FsInodeRegion.bootCells capacity.records records dss nib -∗
      clients capacity names view nib counts imageRecords -∗ registryRows capacity names nib ==∗
      slots capacity names view records dss nib ∗ outside capacity records dss nib) := by
  unfold FsInodeRegion.bootCells clients registryRows slots outside
  rw [← BigSepS.bigSepS_sep.to_eq]
  iintro Hcells Hclients Hregistry
  ihave Hclients := BigSepS.bigSepS_sep.mpr $$ [$Hclients $Hregistry]
  ihave Hall := BigSepS.bigSepS_sep.mpr $$ [$Hcells $Hclients]
  iapply BigSepS.bigSepS_bupd
  iapply BigSepS.bigSepS_mono $$ Hall
  intro z member
  rcases checks with ⟨free, short, ty, count, bare, rec⟩
  have hlink : IcacheRegionSlot.ireg_link_ok (InodeRegionImage.imageDinode dss z) :=
    ⟨free z member, short z member, ty z member⟩
  have hbare : (InodeRegionImage.imageDinode dss z).typeZ = 0 →
      IcacheInodeCustody.ireg_bare (InodeRegionImage.imageDinode dss z) := bare z member
  have cast := FsInodeRegion.inum_cast nib z bound member
  iintro ⟨⟨Hrecord, Hmarker⟩, ⟨Hreference, Hobs, Hcount, Hmirror, Hlink, Htop⟩, Hregistry⟩
  ihave Hlink := IcacheInodeCustody.ireg_lnk_of_at view capacity.links z (counts z) (imageRecords z).typeZ
    (InodeRegionImage.imageDinode dss z) (count z member) (congrArg Dinode.typeZ (rec z member)) $$ Hlink
  isimp only [rec z member] at Htop
  have boot := IcacheRegionSlot.boot_slot capacity names view records (BitVec.ofInt 32 z)
    (InodeRegionImage.imageDinode dss z) 1 1 (iprop(emp)) hlink hbare
  rw [cast] at boot
  imod boot $$ [Hrecord Hmarker Hreference Hobs Hregistry Hcount Hmirror Hlink Htop] with ⟨Hslot, Hout, _⟩
  · unfold IcacheRegionSlot.bootInput
    rw [cast]
    dsimp only
    iframe
  · imodintro
    iframe Hslot Hout

theorem bootstrap_body start blocks counts imageRecords (frame : IProp GF)
    (full : ∀ block ∈ blocks, block.length = 1024)
    (bound : 16 * (blocks.length : Int) ≤ 2 ^ 32)
    (checks : ∀ dss, FsInodeRegion.Decoded blocks dss →
      InodeRegionImage.Premises dss blocks.length counts imageRecords) :
    iprop(FsInodeRegion.regionBytes view start blocks ∗ clients capacity names view blocks.length counts imageRecords ∗
      IcacheEscrowTokens.reg_auth capacity.escrow names.registry ∅ ∗ frame ⊢ |==> ∃ records dss,
      ⌜FsInodeRegion.Decoded blocks dss ∧ InodeRegionImage.Premises dss blocks.length counts imageRecords⌝ ∗
      body capacity names view records start blocks.length ∗ outside capacity records dss blocks.length ∗ frame) := by
  iintro ⟨Hbytes, Hclients, Hregistry, HR⟩
  imod FsInodeRegion.bootstrap_prelude capacity.records view start blocks full bound counts imageRecords checks frame
    $$ [$Hbytes $HR] with ⟨%records, %dss, %decoded, Ha, Hcells, Hrecs, HR⟩
  imod registry_insert capacity names blocks.length $$ Hregistry with ⟨Hregistry, Hrows⟩
  imod slots_from_clients capacity names view records dss blocks.length counts imageRecords bound decoded.2
    $$ Hcells Hclients Hrows with ⟨Hslots, Hout⟩
  ihave Hbody := body_from_rows capacity names view records start blocks dss decoded.1 $$ Ha Hrecs Hslots Hregistry
  imodintro
  iexists records, dss
  iframe Hbody Hout HR
  ipureintro
  exact decoded

theorem actual : Spec capacity where
  bootstrap := fun names view start blocks counts imageRecords frame =>
    bootstrap_body capacity names view start blocks counts imageRecords frame

end MachCSL.Logic.IcacheRegionBoot
