import MachCSL.Logic.FsDurXferRunsDefs
import MachCSL.Logic.FsStateDefs

/-! Source FsDurXfer §§3a–d structural run lists and exactly the lengths
and free-pool domain carried by the native byte footprint. -/
namespace MachCSL.Logic.FsDurXferShape
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState FsDurXferRuns

def recordRun (sb : Superblock) (i : Int) (node : Node) : Run :=
  ((inodeBlock (BitVec.ofInt 32 i) sb.inodestart, (64 * inodeSlot (BitVec.ofInt 32 i) : Nat)), dinodeBytes node.record)
def dataRun (node : Node) (entry : Nat × List MachCSL.Memory.Byte) : Run := ((node.address entry.1, 0), entry.2)
def indirectRuns (node : Node) : List Run :=
  if node.indirect = 0 then [] else [((node.indirect, 0), indirectBytes node.entries)]
def dataRuns (node : Node) : List Run :=
  (FiniteMap.toList (M := FsState.SlotMap) node.blocks).map (dataRun node) ++ indirectRuns node
def inodeRuns (sb : Superblock) (i : Int) (node : Node) : List Run := recordRun sb i node :: dataRuns node
def inodesRuns (sb : Superblock) (nodes : InodeMap) : List Run :=
  (FiniteMap.toList (M := FsState.InodeMap) nodes).flatMap (fun entry => inodeRuns sb entry.1 entry.2)
def poolRuns (pool : BlockMap) : List Run :=
  (FiniteMap.toList (M := Disk.ImageMap) pool).map (fun entry => ((entry.1, 0), entry.2))
def fsRuns (state : State) (pool : BlockMap) : List Run :=
  ((1, 0), state.superblockBytes) ::
  ((state.superblock.bmapstart, 0), BitmapEncoding.bitmapBytes 1024 state.used) ::
  (inodesRuns state.superblock state.inodes ++ poolRuns pool)

structure NodeLens (node : Node) : Prop where
  data : ∀ (k : Nat) bytes, node.blocks[k]? = some bytes → bytes.length = 1024
  indirect : node.indirect ≠ 0 → (indirectBytes node.entries).length = 1024

structure PoolPM (indices : List Int) (used : BlockSet) (pool : BlockMap) : Prop where
  domain : ∀ b : Int, (pool[b]?).isSome ↔ b ∈ indices ∧ b ∉ used
  length : ∀ (b : Int) bytes, pool[b]? = some bytes → bytes.length = 1024

structure Shape (state : State) (pool : BlockMap) : Prop where
  superblock : state.superblockBytes.length = 1024
  nodes : ∀ (i : Int) node, state.inodes[i]? = some node → NodeLens node
  pool : PoolPM (FsState.poolIndices state.superblock.size) state.used pool

end MachCSL.Logic.FsDurXferShape
