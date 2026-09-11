import MachCSL.Logic.FsBytesBootstrapMintProofs

namespace MachCSL.Logic.FsBytesBootstrap
open Iris Iris.Std Iris.BI Iris.Algebra
open FsDurBytes FsBytesInvariant
variable {GF : BundledGFunctors}

private theorem split_halves {V : Type} [GhostMapG GF Int V FsBlockGhost.BlockMap]
    (g : GName) (map : FsBlockGhost.BlockMap V) :
    iprop((bigSepM (M := FsBlockGhost.BlockMap) (fun b v => ghost_map_elem g (.own 1) b v) map : IProp GF) ⊢
      bigSepM (M := FsBlockGhost.BlockMap) (fun b v => ghost_map_elem g (.own (1 : Qp).half) b v) map ∗
      bigSepM (M := FsBlockGhost.BlockMap) (fun b v => ghost_map_elem g (.own (1 : Qp).half) b v) map) := by
  rw [← BigSepM.bigSepM_sep_eq]
  apply BigSepM.bigSepM_mono
  intro b v _
  have split : iprop((ghost_map_elem g (.own 1) b v : IProp GF) ⊣⊢
      ghost_map_elem g (.own (1 : Qp).half) b v ∗ ghost_map_elem g (.own (1 : Qp).half) b v) := by
    simpa only [Qp.half_add_half] using
      (Fractional.fractional (Φ := fun q : Qp => (ghost_map_elem g (.own q) b v : IProp GF))
        (1 : Qp).half (1 : Qp).half)
  exact split.mp

variable {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem fs_alloc (link top : GName) (cache : BlockMap) (home : BlockSet)
    (values : Int → List Byte) (exceptions : BlockSet)
    (full : BlocksFull cache) (homeSub : home ⊆ FiniteMap.dom_set (S := BlockSet) cache)
    (valueFull : ∀ b, b ∈ home → (values b).length = 1024) (exceptionHome : exceptions ⊆ home)
    (agreement : ∀ b bytes, get? cache b = some bytes → b ∈ home → b ∉ exceptions → values b = bytes)
    (E : CoPset) (frame : IProp GF) :
    iprop(frame ⊢ |={E}=> ∃ names : Names,
      allocated capacity link top names cache home values exceptions ∗ frame) := by
  letI := capacity.blocks.cache
  letI := capacity.blocks.dirty
  iintro Hframe
  imod (ghost_map_alloc cache) with ⟨%gc, Hca, HC⟩
  imod (ghost_map_alloc (cleanMap cache)) with ⟨%gd, Hda, HD⟩
  ihave ⟨HCm, HCp⟩ := split_halves gc cache $$ HC
  ihave ⟨HDm, HDp⟩ := split_halves gd (cleanMap cache) $$ HD
  ihave ⟨HCh, HCl⟩ := (filter_split cache home
    (fun b bs => ghost_map_elem gc (.own (1 : Qp).half) b bs)).mp $$ HCp
  let names : Names := ⟨gc, gd, 1, link, top, 1⟩
  have domain := homeMap_domain cache home homeSub
  have homelen : ∀ b, b ∈ FiniteMap.dom_set (S := BlockSet) (homeMap cache home) → (values b).length = 1024 := by
    simpa only [domain] using valueFull
  have exceptionHome' : exceptions ⊆ FiniteMap.dom_set (S := BlockSet) (homeMap cache home) := by
    simpa only [domain] using exceptionHome
  have agreement' : ∀ b bs, get? (homeMap cache home) b = some bs → b ∉ exceptions → values b = bs := by
    intro b bs found outside
    obtain ⟨found, inside⟩ := (homeMap_get cache home b bs).mp found
    exact agreement b bs found inside outside
  have mint := fs_bytes_alloc capacity names (homeMap cache home) values exceptions
    (homeMap_full cache home full) homelen exceptionHome' agreement' E frame
  unfold cacheHalves FsBlockGhost.chalf FsBlockGhost.cacheElem at mint
  imod mint $$ HCh Hframe with ⟨%gL, %gX, Hi, Hxo, Hfb, Hframe⟩
  isimp only [domain] at Hi
  imodintro
  iexists (withBytes names gL gX)
  unfold allocated withBytes names
  isimp only [withBytes, names] at Hi
  iframe Hframe Hi Hxo Hfb
  isplit
  · ipureintro; rfl
  · isplit
    · ipureintro; rfl
    · unfold FsBlockGhost.cacheAuth FsBlockGhost.dirtyAuth
      iframe Hca Hda
      isplitl [HCm HDm HDp]
      · unfold machinery FsBlockGhost.mclean FsBlockGhost.chalf FsBlockGhost.cacheElem
        unfold FsBlockGhost.dirtyHalf FsBlockGhost.dirtyElem
        isimp only [cleanMap, BigOpM.bigOpM_map_eq] at HDm HDp
        rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]
        iframe
      · unfold cacheHalves FsBlockGhost.chalf FsBlockGhost.cacheElem
        iexact HCl

theorem actual : Spec capacity :=
  ⟨byte_map_grow capacity, fs_bytes_alloc capacity, fs_alloc capacity⟩

end MachCSL.Logic.FsBytesBootstrap
