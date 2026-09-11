import Xv6.Fs.InodeRegionImageProofs

namespace Xv6.Fs.SnapshotConfig
open DurableState SnapshotHome InodeRegionImage

/-- Exact FsCfgSnap.snap_ireg_premises: all six decoded-region conditions
follow from the named snapshot records and their source Local facts. -/
theorem snap_ireg_premises state image home (blocks : List (List Dinode)) (nib : Nat)
    (full : BlocksFull image) (bytes : Snapshot.Bytes state (restrict image home))
    (hlocal : DurableState.Local state)
    (width : (nib : Int) = state.superblock.ninodes / 16 + 1)
    (bound : 16 * (nib : Int) ≤ 2 ^ 32) (length : blocks.length = nib)
    (wellFormed : ∀ records ∈ blocks, InodeBlockWellFormed records)
    (encoded : ∀ bi : Nat, bi < nib → image (state.superblock.inodestart + (bi : Int)) = inodeBlockBytes (blocks[bi]?.getD [])) :
    InodeRegionImage.Premises blocks nib (fun i => (node state i).nlink) (fun i => (node state i).record) := by
  have decoded i (member : i ∈ regionInums nib) : imageDinode blocks i = (node state i).record := by
    rw [image_dinode_fs_dinode image state.superblock blocks nib i length wellFormed encoded
      ((region_inums_spec nib i).mp member) bound]
    exact snap_rec_decode_region state image home nib i full bytes width member
  have localNode i (member : i ∈ regionInums nib) : DurableNode.Local i (node state i) :=
    hlocal i (node state i) (snap_node_at state _ nib i bytes width member)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i member free
    rw [decoded i member] at free ⊢
    have zero := (localNode i member).free free
    change ((node state i).record.nlink.toNat : Int) = 0
    change (node state i).record.nlink.toNat = 0 at zero
    omega
  · intro i member
    rw [decoded i member]
    exact (localNode i member).nlink
  · intro i member
    rw [decoded i member]
    exact (localNode i member).type
  · intro i member
    rw [decoded i member]
    rfl
  · intro i member free
    rw [decoded i member] at free ⊢
    exact ireg_bare_of_fn_bare _ ((localNode i member).bareFree free)
  · intro i member
    exact (decoded i member).symm

end Xv6.Fs.SnapshotConfig
