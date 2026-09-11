import Xv6.Fs.TreeDefs
import Xv6.Fs.InodeValidityDefs

/-! Full source FsNode carrier and FsStateInode readers. This carrier keeps
allocated blocks beyond file size and is distinct from the file-tree node. -/
namespace Xv6.Fs.DurableNode

abbrev SlotMap := Std.ExtTreeMap Nat (List (BitVec 8))

structure Node where
  record : Dinode
  entries : List (BitVec 32)
  blocks : SlotMap

namespace Node

def typeZ (n : Node) : Int := n.record.typeZ
def sizeZ (n : Node) : Int := n.record.sizeZ
def nlink (n : Node) : Nat := n.record.nlink.toNat
def address (n : Node) (k : Nat) : Int :=
  if k < 12 then n.record.addrZ k else (n.entries[k - 12]?.getD 0).toNat
def indirect (n : Node) : Int := n.record.addrZ 12
def data (n : Node) (k : Nat) : List (BitVec 8) :=
  n.blocks[k]?.getD (List.replicate 1024 0)
def nrec (n : Node) : Nat := dirNrec n.sizeZ
def bytes (n : Node) : List (BitVec 8) := fileBytes n.data n.sizeZ.toNat
def isDir (n : Node) : Bool := n.typeZ == 1
def dirEntries (n : Node) : NameMap := if n.isDir then dirView n.data n.nrec else ∅
def orphan (n : Node) : Bool := n.nlink == 0

/-- Data-slot footprint and indirect-root footprint; no file-size restriction. -/
def Owns (n : Node) (b : Int) : Prop :=
  (∃ k, n.blocks[k]?.isSome ∧ n.address k = b) ∨ (n.indirect ≠ 0 ∧ n.indirect = b)

def slot (n : Node) (k : Nat) : Int := if k = 268 then n.indirect else n.address k
def SlotInjective (n : Node) : Prop :=
  ∀ k j : Nat, k ≤ 268 → j ≤ 268 → n.slot k ≠ 0 → n.slot k = n.slot j → k = j

/-- Source bare node: includes zero links, entries and the empty owned map. -/
def Bare (n : Node) : Prop :=
  n.record.addrs = List.replicate 13 0 ∧ n.entries = List.replicate 256 0 ∧
  n.blocks = ∅ ∧ n.sizeZ = 0 ∧ n.nlink = 0

end Node

/-- Exact sparse first-winner recursion from FsStateEra.blk_of_seq. -/
def blocksOfSeq (f : Nat → Option (List (BitVec 8))) (start : Nat) : Nat → SlotMap
  | 0 => ∅
  | count + 1 => match f start with
    | some bytes => (blocksOfSeq f (start + 1) count).insert start bytes
    | none => blocksOfSeq f (start + 1) count

/-- Build the data component for all 268 possible slots, including allocations
beyond size. Entries and data remain the caller's exact values. -/
def nodeOf (record : Dinode) (entries : List (BitVec 32)) (data : FileData) : Node :=
  let skeleton : Node := ⟨record, entries, ∅⟩
  ⟨record, entries, blocksOfSeq
    (fun k => if skeleton.address k = 0 then none else some (data k)) 0 268⟩

def zero : Node :=
  ⟨⟨0, 0, 0, 0, 0, List.replicate 13 0⟩, List.replicate 256 0, ∅⟩

end Xv6.Fs.DurableNode
