import Xv6.Fs.SnapshotCoverageDefs

/-! Pure FsCfgSnap source configuration vocabulary. Total node lookup keeps
the source's malformed empty-list default; block sets retain every map key. -/
namespace Xv6.Fs.SnapshotConfig
open DurableState

def defaultNode : DurableNode.Node := ⟨⟨0, 0, 0, 0, 0, []⟩, [], ∅⟩
def node (state : State) (i : Int) : DurableNode.Node := state.inodes[i]?.getD defaultNode

def regionInums (nib : Nat) : BlockSet :=
  Std.ExtTreeSet.ofList ((List.range (16 * nib)).map Int.ofNat)

def regionBlocks (start : Int) (nib : Nat) : BlockSet :=
  Std.ExtTreeSet.ofList ((List.range nib).map (fun i : Nat => start + (i : Int)))

def blockSet (n : DurableNode.Node) : BlockSet :=
  Std.ExtTreeSet.ofList (n.blocks.toList.map (fun entry => n.address entry.1)) ∪
    (if n.indirect = 0 then ∅ else (∅ : BlockSet).insert n.indirect)

def liveBlocks (state : State) (inums : BlockSet) : BlockSet :=
  inums.toList.foldr (fun i all => blockSet (node state i) ∪ all) ∅

def freeSet (count : Int) (used : BlockSet) : BlockSet :=
  Std.ExtTreeSet.ofList ((List.range count.toNat).map Int.ofNat) \ used

def bitmapSpent (state : State) : BlockSet :=
  (∅ : BlockSet).insert state.superblock.bmapstart ∪ freeSet state.superblock.size state.used

def liveSet (state : State) (nib : Nat) : BlockSet :=
  (regionInums nib).filter (fun i => (node state i).typeZ != 0)

def spent (state : State) (nib : Nat) : BlockSet :=
  ((∅ : BlockSet).insert 1 ∪ SnapshotHome.logRegion state.superblock.logstart ∪
    regionBlocks state.superblock.inodestart nib ∪ bitmapSpent state) ∪ liveBlocks state (liveSet state nib)

end Xv6.Fs.SnapshotConfig
