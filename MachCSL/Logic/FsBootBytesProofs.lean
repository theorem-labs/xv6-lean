import MachCSL.Logic.FsBootBytesCarveProofs
import MachCSL.Logic.FsBytesBootstrapProofs

set_option maxRecDepth 2048

namespace MachCSL.Logic.FsBootBytes
open Iris Iris.Std Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

theorem fs_boot_ghosts diskNames disk length covered home device link top values exceptions
    (bound : Xv6.Fs.CovIn covered length) (homeSub : home ⊆ covered)
    (valuesFull : ∀ b, b ∈ home → (values b).length = 1024) (exceptionHome : exceptions ⊆ home)
    (agreement : ∀ b, b ∈ home → b ∉ exceptions → values b = Xv6.Fs.blocks disk b)
    (E : CoPset) (frame : IProp GF) :
    iprop(⊢ DiskClient.diskBytes capacity.bytes diskNames 0 (Devices.Virtio.disk_read disk 0 length) -∗
      frame ={E}=∗ ∃ names : Names,
      allocated capacity diskNames disk covered home device link top names values exceptions ∗
      remainder capacity diskNames disk length covered ∗ frame) := by
  have homeSub' : home ⊆ FiniteMap.dom_set (M := Disk.ImageMap) (S := BlockSet) (rawMap disk covered) := by
    rw [rawMap_domain]; exact homeSub
  have agree' : ∀ b bytes, get? (M := Disk.ImageMap) (rawMap disk covered) b = some bytes →
      b ∈ home → b ∉ exceptions → values b = bytes := by
    intro b bytes found hin hout
    obtain ⟨_, rfl⟩ := (rawMap_lookup disk covered b bytes).mp found
    exact agreement b hin hout
  iintro Hbytes Hframe
  ihave ⟨Hphysical, Hrest, Hframe⟩ := carve capacity diskNames disk length covered bound frame $$ [$Hbytes $Hframe]
  imod FsBytesBootstrap.fs_alloc capacity link top (rawMap disk covered) home values exceptions
    (rawMap_full disk covered) homeSub' valuesFull exceptionHome agree' E
    (iprop(remainder capacity diskNames disk length covered ∗ frame)) $$ [$Hrest $Hframe]
    with ⟨%names, Ha, Hrestframe⟩
  iunfold FsBytesBootstrap.allocated at Ha
  ihave ⟨%sameLink, %sameTop, Hcache, Hdirty, Hinv, Hexception, Hmachinery, Hhome, Houtside⟩ := Ha
  isimp only [FsBytesBootstrap.machinery, BigSepM.bigSepM_sep_eq] at Hmachinery
  ihave ⟨Hclean, HdirtyHalf⟩ := Hmachinery
  ihave HcleanSet := (map_to_set (FsBlockGhost.mclean capacity.blocks names) disk covered).mp $$ Hclean
  ihave HdirtySet := (map_to_set (fun b _ => FsBlockGhost.dirtyHalf capacity.blocks names b false) disk covered).mp $$ HdirtyHalf
  isimp only [FsBytesBootstrap.committedRuns, rawMap_filter_in disk covered home homeSub] at Hhome
  ihave HhomeSet := (map_to_set (fun b _ => FsBlocks.block capacity.bytes names.bytes b (values b)) disk home).mp $$ Hhome
  isimp only [FsBytesInvariant.cacheHalves, rawMap_filter_out] at Houtside
  ihave HoutsideSet := (map_to_set (FsBlockGhost.chalf capacity.blocks names) disk (covered \ home)).mp $$ Houtside
  imodintro
  iexists names
  unfold allocated
  iframe Hrestframe Hcache Hinv Hexception HdirtySet HhomeSet HoutsideSet
  isplit
  · ipureintro; exact sameLink
  · isplit
    · ipureintro; exact sameTop
    · unfold dirtyMap
      iframe Hdirty
      iunfold physicalBlocks at Hphysical
      ihave Hboth := BigSepS.bigSepS_sep.mpr $$ [$Hphysical $HcleanSet]
      iapply BigSepS.bigSepS_mono $$ Hboth
      intro b _
      iintro ⟨Hphysical, Hclean⟩
      unfold BioView.poolBlock fsView
      iexists (Xv6.Fs.blocks disk b)
      iframe

theorem actual : Spec capacity := ⟨fs_boot_ghosts capacity⟩

end MachCSL.Logic.FsBootBytes
