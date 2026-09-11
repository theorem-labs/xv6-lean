import Xv6.Fs.InodeValidityDefs

/-! Source FsImg.v §§5/9: duplicate-free collection and exact W4/W5 inputs. -/
namespace Xv6.Fs

abbrev BlockSet := Std.ExtTreeSet Int

/-- Process the tail first, rejecting a repeated head, exactly as `gset_nodup`. -/
def collectNodup : List Int → Option BlockSet
  | [] => some ∅
  | x :: xs => match collectNodup xs with
    | none => none
    | some s => if x ∈ s then none else some (s.insert x)

/-- Indirect block first, then direct content blocks, then indirect content.
Malformed records retain the source's truncation and total-lookup behavior. -/
def inodeBlocks (image : Blocks) (dn : Dinode) : List Int :=
  let nb := nblk dn.sizeZ
  let es := indirectEntries image dn
  (if 12 < nb then [dn.addrZ 12] else []) ++
    ((List.range (min nb 12).toNat).map dn.addrZ ++
    (List.range (nb - 12).toNat).map (fun j => es[j]?.getD 0))

/-- Untrusted inputs can be used only after equality with the original readers. -/
def inodeBlocksInput (dn : Dinode) (entries : List Int) : List Int :=
  let nb := nblk dn.sizeZ
  (if 12 < nb then [dn.addrZ 12] else []) ++
    ((List.range (min nb 12).toNat).map dn.addrZ ++
    (List.range (nb - 12).toNat).map (fun j => entries[j]?.getD 0))

def usedBlocks (image : Blocks) (sb : Superblock) : List Int :=
  ((List.range sb.ninodes.toNat).map fun (i : Nat) =>
    let dn := dinode image sb (i : Int)
    if dn.typeZ == 0 then [] else inodeBlocks image dn).flatten

def usedSet (image : Blocks) (sb : Superblock) : Option BlockSet :=
  collectNodup (usedBlocks image sb)

def inodeBlockSet (image : Blocks) (sb : Superblock) (inum : Int) : BlockSet :=
  Std.ExtTreeSet.ofList (inodeBlocks image (dinode image sb inum))

/-- Source Euclidean division/modulo followed by Z.to_nat for the byte index.
In particular, negative bit addresses are not silently rejected. -/
def bitmapBit (bytes : List (BitVec 8)) (bit : Int) : Bool :=
  (bytes[(bit / 8).toNat]?.getD 0).getLsbD (bit % 8).toNat

/-- Only blocks below `size` are checked; the remaining bitmap tail is unconstrained. -/
def bitmapValid (image : Blocks) (sb : Superblock) (used : BlockSet) : Bool :=
  (List.range sb.size.toNat).all fun i =>
    bitmapBit (image sb.bmapstart) (i : Int) ==
      (decide ((i : Int) < dataStart sb) || decide ((i : Int) ∈ used))

def bitmapSet (n : Nat) (bytes : List (BitVec 8)) : BlockSet :=
  Std.ExtTreeSet.ofList (((List.range (8 * n)).map Int.ofNat).filter (bitmapBit bytes))

/-- Exact W4/W5 arm of the source image checker. -/
def blocksBitmapValid (image : Blocks) (sb : Superblock) : Bool :=
  match usedSet image sb with
  | none => false
  | some used => bitmapValid image sb used

end Xv6.Fs
