import MachCSL.Logic.FsDurBytesDefs
import Xv6.Fs.SnapshotDefs

/-! Exact six-slot footprint from FsDurAlloc.v. Definitions remain total on
arbitrary states; snapshot hypotheses belong to the separate proof interface. -/
namespace MachCSL.Logic.FsDurAlloc
open Iris Iris.Std Iris.BI Xv6.Fs
open DurableState DurableNode

inductive Slot where
  | sb
  | bmap
  | record (inode : Int)
  | data (inode : Int) (slot : Nat)
  | indirect (inode : Int)
  | pool (block : Int)
  deriving DecidableEq

/-- FsNode.v's inhabitant, including empty address and entry lists.
This is deliberately distinct from the well-shaped bare `DurableNode.zero`. -/
def sourceDefault : Node := ⟨⟨0, 0, 0, 0, 0, []⟩, [], ∅⟩

def nodeAt (state : State) (inode : Int) : Node :=
  state.inodes[inode]?.getD sourceDefault

def fpRun (block offset : Int) (bytes : List (BitVec 8)) : FsDurBytes.ByteMap :=
  FsDurBytes.byteRun (block * 1024 + offset) bytes

def fpBlock (state : State) : Slot → Int
  | .sb => 1
  | .bmap => state.superblock.bmapstart
  | .record i => state.superblock.inodestart + i / 16
  | .data i k => (nodeAt state i).address k
  | .indirect i => (nodeAt state i).indirect
  | .pool b => b

def fpOffset : Slot → Int
  | .record i => 64 * (i % 16)
  | _ => 0

def fpBytes (state : State) (disk : BlockMap) : Slot → List (BitVec 8)
  | .sb => state.superblockBytes
  | .bmap => BitmapEncoding.bitmapBytes 1024 state.used
  | .record i => dinodeBytes (nodeAt state i).record
  | .data i k => (nodeAt state i).blocks[k]?.getD []
  | .indirect i => if (nodeAt state i).indirect = 0 then [] else indirectBytes (nodeAt state i).entries
  | .pool b => if b ∈ state.used then [] else disk[b]?.getD []

def fpMap (state : State) (disk : BlockMap) (slot : Slot) : FsDurBytes.ByteMap :=
  fpRun (fpBlock state slot) (fpOffset slot) (fpBytes state disk slot)

def Valid (state : State) : Slot → Prop
  | .sb | .bmap => True
  | .record i | .indirect i => state.inodes[i]?.isSome
  | .data i k => state.inodes[i]?.isSome ∧ (nodeAt state i).blocks[k]?.isSome
  | .pool b => 0 ≤ b ∧ b < state.superblock.size

def metadataClass : Slot → Bool
  | .sb | .bmap | .record _ => true
  | _ => false

/-- Only order within a finite key enumeration differs by map implementation;
subsequent laws use membership, uniqueness, and separation. -/
def inodes (state : State) : List Int := state.inodes.keys

def records (state : State) : List Slot := (inodes state).map Slot.record

def dataSlots (state : State) : List Slot :=
  (inodes state).flatMap fun i => (nodeAt state i).blocks.keys.map (Slot.data i)

def indirects (state : State) : List Slot := (inodes state).map Slot.indirect

def pools (state : State) : List Slot :=
  (List.range state.superblock.size.toNat).map fun b => Slot.pool (Int.ofNat b)

def family (state : State) : List Slot :=
  .sb :: .bmap :: (records state ++ dataSlots state ++ indirects state ++ pools state)

/-- The selected union has an explicit left-biased fold even for malformed
families; its resource law requires the stated pairwise separation. -/
def selected {A : Type} (slots : List A) (maps : A → FsDurBytes.ByteMap) : FsDurBytes.ByteMap :=
  slots.foldr (fun slot rest => FsDurBytes.leftUnion (maps slot) rest) ∅

def slotLedger {GF : BundledGFunctors} (view : FsView.View GF)
    (state : State) (disk : BlockMap) : IProp GF :=
  bigSepL (fun _ slot => FsView.byteRange view (fpBlock state slot)
    (fpOffset slot) (fpBytes state disk slot)) (family state)

end MachCSL.Logic.FsDurAlloc
