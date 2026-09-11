import Xv6.Fs.Dinode
import Std.Data.ExtTreeSet

/-! Exact W3 and full-region checks from `iris/FsImg.v:684–751,962–1311`
at xv6iris arxiv-v1. These are the boot-image checks, not the later durable DWF.
Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
-/
namespace Xv6.Fs

/-- Signed source arithmetic, including negative inputs. -/
def nblk (size : Int) : Int := (size + 1023) / 1024
def nblocks (size : Int) : Nat := (nblk size).toNat

def Dinode.typeZ (dn : Dinode) : Int := dn.type.toNat
def Dinode.nlinkZ (dn : Dinode) : Int := dn.nlink.toNat
def Dinode.sizeZ (dn : Dinode) : Int := dn.size.toNat
def Dinode.addrZ (dn : Dinode) (k : Nat) : Int := (dn.addrs[k]?.getD 0).toNat

def addrValid (sb : Superblock) (address : Int) : Bool :=
  decide (dataStart sb ≤ address) && decide (address < sb.size)

/-- W3 requires unused direct and indirect entries to be zero. It deliberately
skips no field on the basis of a later durable-filesystem specification. -/
def inodeValid (image : Blocks) (sb : Superblock) (dn : Dinode) : Bool :=
  let nb := nblk dn.sizeZ
  let ib := dn.addrZ 12
  let entries := indirectEntries image dn
  (dn.typeZ == 1 || dn.typeZ == 2 || dn.typeZ == 3) &&
  decide (1 ≤ dn.nlinkZ) && decide (dn.sizeZ ≤ 268 * 1024) &&
  (List.range 12).all (fun k =>
    if (k : Int) < nb then addrValid sb (dn.addrZ k) else dn.addrZ k == 0) &&
  (if nb ≤ 12 then ib == 0 else addrValid sb ib) &&
  (List.range 256).all (fun j =>
    if (j : Int) < nb - 12 then addrValid sb (entries[j]?.getD 0)
    else entries[j]?.getD 0 == 0)

/-- The nine source `fs_inode_ok` fields; the arbitrary address-list carrier
and total lookup defaults are unchanged. -/
structure InodeOK (image : Blocks) (sb : Superblock) (dn : Dinode) : Prop where
  type : dn.typeZ = 1 ∨ dn.typeZ = 2 ∨ dn.typeZ = 3
  nlink : 1 ≤ dn.nlinkZ
  size : dn.sizeZ ≤ 268 * 1024
  direct : ∀ k : Nat, k < 12 → (k : Int) < nblk dn.sizeZ →
    dataStart sb ≤ dn.addrZ k ∧ dn.addrZ k < sb.size
  direct_zero : ∀ k : Nat, k < 12 → nblk dn.sizeZ ≤ (k : Int) → dn.addrZ k = 0
  ind_zero : nblk dn.sizeZ ≤ 12 → dn.addrZ 12 = 0
  ind : 12 < nblk dn.sizeZ → dataStart sb ≤ dn.addrZ 12 ∧ dn.addrZ 12 < sb.size
  ent : ∀ j : Nat, j < 256 → (j : Int) < nblk dn.sizeZ - 12 →
    dataStart sb ≤ (indirectEntries image dn)[j]?.getD 0 ∧
      (indirectEntries image dn)[j]?.getD 0 < sb.size
  ent_zero : ∀ j : Nat, j < 256 → nblk dn.sizeZ - 12 ≤ (j : Int) →
    (indirectEntries image dn)[j]?.getD 0 = 0

def inodesValid (image : Blocks) (sb : Superblock) : Bool :=
  (List.range sb.ninodes.toNat).all fun i =>
    let dn := dinode image sb (i : Int)
    if dn.typeZ == 0 then true else inodeValid image sb dn

/-- Sweep every record in the allocated inode region, including its rounded tail. -/
def regionFree (image : Blocks) (sb : Superblock) (nib : Nat) : Bool :=
  (List.range (16 * nib)).all fun i =>
    if (i : Int) < sb.ninodes then true else (dinode image sb (i : Int)).typeZ == 0

def regionNlink (image : Blocks) (sb : Superblock) (nib : Nat) : Bool :=
  (List.range (16 * nib)).all fun i =>
    let dn := dinode image sb (i : Int)
    (if dn.typeZ == 0 then dn.nlinkZ == 0 else true) && decide (dn.nlinkZ ≤ 32767)

/-- Source bare-record check traverses the whole arbitrary address list. -/
def recordBare (dn : Dinode) : Bool :=
  dn.sizeZ == 0 && dn.addrs.all (fun a => a.toNat == 0)

def regionBare (image : Blocks) (sb : Superblock) (nib : Nat) : Bool :=
  (List.range (16 * nib)).all fun i =>
    let dn := dinode image sb (i : Int)
    if dn.typeZ == 0 then recordBare dn else true

/-- Exactly the source bundle. Bare records are a separate premise. -/
def regionValid (image : Blocks) (sb : Superblock) (nib : Nat) : Bool :=
  regionFree image sb nib && regionNlink image sb nib

/-- Ordered enumeration; negative inode counts enumerate nothing, as Z.to_nat. -/
def liveInodes (image : Blocks) (sb : Superblock) : List Int :=
  ((List.range sb.ninodes.toNat).map Int.ofNat).filter fun z =>
    !((dinode image sb z).typeZ == 0)

/-- Concrete finite extensional set corresponding to source `list_to_set`. -/
def liveSet (image : Blocks) (sb : Superblock) : Std.ExtTreeSet Int :=
  Std.ExtTreeSet.ofList (liveInodes image sb)

end Xv6.Fs
