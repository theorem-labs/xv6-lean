import Xv6.Fs.SnapshotConfigDefs

/-! Exact pure IcacheBoot image decoding and six inode-region premises.
The total double lookup uses the source empty-list/empty-address defaults. -/
namespace Xv6.Fs.InodeRegionImage
open SnapshotConfig

def imageDinode (blocks : List (List Dinode)) (i : Int) : Dinode :=
  ((blocks[(i / 16).toNat]?).getD [])[(i % 16).toNat]?.getD default

def bare (record : Dinode) : Prop :=
  record.sizeZ = 0 ∧ record.addrs = List.replicate 13 0

def typeOK (record : Dinode) : Prop :=
  record.typeZ = 0 ∨ record.typeZ = 1 ∨ record.typeZ = 2 ∨ record.typeZ = 3

def nlink (record : Dinode) : Nat := record.nlink.toNat

def imageFreeNlink (blocks : List (List Dinode)) (nib : Nat) : Prop :=
  ∀ i, i ∈ regionInums nib → (imageDinode blocks i).typeZ = 0 → (imageDinode blocks i).nlinkZ = 0

def imageNlinkShort (blocks : List (List Dinode)) (nib : Nat) : Prop :=
  ∀ i, i ∈ regionInums nib → (imageDinode blocks i).nlinkZ ≤ 32767

def imageTypeOK (blocks : List (List Dinode)) (nib : Nat) : Prop :=
  ∀ i, i ∈ regionInums nib → typeOK (imageDinode blocks i)

def imageNlinkAt (counts : Int → Nat) (blocks : List (List Dinode)) (nib : Nat) : Prop :=
  ∀ i, i ∈ regionInums nib → counts i = nlink (imageDinode blocks i)

def imageBare (blocks : List (List Dinode)) (nib : Nat) : Prop :=
  ∀ i, i ∈ regionInums nib → (imageDinode blocks i).typeZ = 0 → bare (imageDinode blocks i)

def imageRecordAt (records : Int → Dinode) (blocks : List (List Dinode)) (nib : Nat) : Prop :=
  ∀ i, i ∈ regionInums nib → records i = imageDinode blocks i

def Premises (blocks : List (List Dinode)) (nib : Nat) (counts : Int → Nat) (records : Int → Dinode) : Prop :=
  imageFreeNlink blocks nib ∧ imageNlinkShort blocks nib ∧ imageTypeOK blocks nib ∧
  imageNlinkAt counts blocks nib ∧ imageBare blocks nib ∧ imageRecordAt records blocks nib

end Xv6.Fs.InodeRegionImage
