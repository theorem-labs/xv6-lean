import MachCSL.Logic.FsStateSpec
import MachCSL.Logic.FsStateInodeProofs
import MachCSL.Logic.FsStateBitmapProofs

namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Xv6.Fs FsView
variable {GF : BundledGFunctors} (view : View GF) (capacity : FsLink.Capacity GF)

instance sbOwned_timeless [GTimeless view] sb bytes : Timeless (sbOwned view sb bytes) := by
  unfold sbOwned; infer_instance
instance fsInodes_timeless [GTimeless view] sb nodes : Timeless (fsInodes view capacity sb nodes) := by
  unfold fsInodes; infer_instance
instance state_timeless [GTimeless view] dq s : Timeless (state view capacity dq s) := by
  unfold state; infer_instance
instance footprint_timeless [GTimeless view] dq s : Timeless (footprint view dq s) := by
  unfold footprint; infer_instance
instance ghost_timeless s : Timeless (ghost view capacity s) := by
  unfold ghost; infer_instance
instance pureState_timeless s : Timeless (pureState (GF := GF) s) := by
  unfold pureState; infer_instance
instance pureState_persistent s : Persistent (pureState (GF := GF) s) := by
  unfold pureState; infer_instance
instance linkNode_timeless γ i n : Timeless (linkNode capacity γ i n) := by
  unfold linkNode
  have (ty : FsLink.IType) (types : FName → FsLink.IType) :
      Timeless (iOwn (E := capacity.link) γ (LinkFamily.nodeElem i n ty types)) :=
    iOwn_timeless (E := capacity.link)
  infer_instance
instance links_timeless γ nodes : Timeless (links capacity γ nodes) := by
  unfold links; infer_instance

theorem state_gammaQ dq s : state view capacity dq s = state (gammaQ view dq) capacity (.own 1) s := rfl
theorem footprint_gammaQ dq s : footprint view dq s = footprint (gammaQ view dq) (.own 1) s := rfl
theorem footprint_names (g t : GName) dq s : footprint view dq s = footprint ⟨view.phi, g, t⟩ dq s := rfl

theorem state_geometry dq s : state view capacity dq s ⊢ ⌜DurableState.Geometry s⌝ := by
  unfold state
  iintro ⟨_, _, _, H⟩
  iexact H

theorem pureState_geometry s : pureState (GF := GF) s ⊢ ⌜DurableState.Geometry s⌝ := by
  unfold pureState
  iintro ⟨_, _, H⟩
  iexact H

theorem fsInodes_acc sb nodes i n (found : nodes[i]? = some n) :
    fsInodes view capacity sb nodes ⊣⊢ inodeOwned view capacity sb i n ∗
      (inodeOwned view capacity sb i n -∗ fsInodes view capacity sb nodes) := by
  unfold fsInodes
  exact BigSepM.bigSepM_lookup_acc (M := InodeMap) found

theorem state_inode_acc dq s i n (found : s.inodes[i]? = some n) :
    state view capacity dq s ⊢ inodeOwned (gammaQ view dq) capacity s.superblock i n ∗
      (inodeOwned (gammaQ view dq) capacity s.superblock i n -∗ state view capacity dq s) := by
  unfold state
  iintro ⟨Hsb, Hi, Hbm, Hg⟩
  ihave ⟨Hn, Hback⟩ := (fsInodes_acc (gammaQ view dq) capacity s.superblock s.inodes i n found).mp $$ Hi
  isplitl [Hn]
  · iexact Hn
  · iintro Hn
    ihave Hi := Hback $$ Hn
    iframe Hsb Hi Hbm Hg

theorem state_split dq s :
    state view capacity dq s ⊣⊢ footprint view dq s ∗ ghost view capacity s := by
  unfold state footprint ghost sbOwned fsInodes inodeOwned freeBitmap freeBitmapAt
  rw [BigSepM.bigSepM_sep_eq]
  rw [show (fun i n => inodeGhost (gammaQ view dq) capacity i n) =
    (fun i n => inodeGhost view capacity i n) from rfl]
  constructor
  · iintro ⟨⟨Hsb, Hp⟩, ⟨Hbytes, Hghost⟩, ⟨Hbitmap, Hpool⟩, Hg⟩
    isplitl [Hsb Hbytes Hbitmap Hpool]
    · iframe Hsb Hbytes Hbitmap Hpool
    · iframe Hp Hghost Hg
  · iintro ⟨⟨Hsb, Hbytes, Hbitmap, Hpool⟩, ⟨Hp, Hghost, Hg⟩⟩
    iframe Hsb Hp Hbytes Hghost Hbitmap Hpool Hg

theorem actual : ResourceSpec view capacity where
  inodeLocal := inodeOwned_local view capacity
  geometry := state_geometry view capacity
  factoring := state_split view capacity
  byteShare := state_gammaQ view capacity
  ghostShare := gammaQ_inodeGhost view capacity

end MachCSL.Logic.FsState
