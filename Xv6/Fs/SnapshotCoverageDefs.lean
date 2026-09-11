import Xv6.Fs.SnapshotDefs
import Xv6.Fs.SnapshotHomeDefs

/-! FsDurSnap.v:1451: every metadata, node-owned or free-pool block named
by a durable snapshot. This predicate does not assume well-formedness. -/
namespace Xv6.Fs.SnapshotCoverage
open DurableState

def Names (state : State) (b : Int) : Prop :=
  Metadata state b ∨
  (∃ (i : Int) (n : DurableNode.Node), state.inodes[i]? = some n ∧ n.Owns b) ∨
  (0 ≤ b ∧ b < state.superblock.size) ∧ b ∉ state.used

end Xv6.Fs.SnapshotCoverage
