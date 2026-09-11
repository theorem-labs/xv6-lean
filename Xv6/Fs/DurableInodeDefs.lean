import Xv6.Fs.InodeValidityDefs

namespace Xv6.Fs

/-- FsImg.v2466: live zero-link orphans and valid allocated entries beyond size are allowed. -/
def inodeDurableValid (image : Blocks) (sb : Superblock) (dn : Dinode) : Bool :=
  let nb := nblk dn.sizeZ
  let ib := dn.addrZ 12
  let entries := indirectEntries image dn
  (dn.typeZ == 1 || dn.typeZ == 2 || dn.typeZ == 3) &&
  decide (dn.sizeZ ≤ 268 * 1024) &&
  (List.range 12).all (fun k =>
    if (k : Int) < nb then addrValid sb (dn.addrZ k)
    else dn.addrZ k == 0 || addrValid sb (dn.addrZ k)) &&
  (if nb ≤ 12 then ib == 0 || addrValid sb ib else addrValid sb ib) &&
  (List.range 256).all (fun j =>
    if (j : Int) < nb - 12 then addrValid sb (entries[j]?.getD 0)
    else entries[j]?.getD 0 == 0 || addrValid sb (entries[j]?.getD 0))

/-- The exact eight source fs_inode_dok fields. -/
structure InodeDurableOK (image : Blocks) (sb : Superblock) (dn : Dinode) : Prop where
  type : dn.typeZ = 1 ∨ dn.typeZ = 2 ∨ dn.typeZ = 3
  size : dn.sizeZ ≤ 268 * 1024
  direct : ∀ k : Nat, k < 12 → (k : Int) < nblk dn.sizeZ →
    dataStart sb ≤ dn.addrZ k ∧ dn.addrZ k < sb.size
  direct_ok : ∀ k : Nat, k < 12 → dn.addrZ k ≠ 0 →
    dataStart sb ≤ dn.addrZ k ∧ dn.addrZ k < sb.size
  ind_ok : dn.addrZ 12 ≠ 0 → dataStart sb ≤ dn.addrZ 12 ∧ dn.addrZ 12 < sb.size
  ind : 12 < nblk dn.sizeZ → dataStart sb ≤ dn.addrZ 12 ∧ dn.addrZ 12 < sb.size
  ent : ∀ j : Nat, j < 256 → (j : Int) < nblk dn.sizeZ - 12 →
    dataStart sb ≤ (indirectEntries image dn)[j]?.getD 0 ∧
      (indirectEntries image dn)[j]?.getD 0 < sb.size
  ent_ok : ∀ j : Nat, j < 256 → (indirectEntries image dn)[j]?.getD 0 ≠ 0 →
    dataStart sb ≤ (indirectEntries image dn)[j]?.getD 0 ∧
      (indirectEntries image dn)[j]?.getD 0 < sb.size

def inodesDurableValid (image : Blocks) (sb : Superblock) : Bool :=
  (List.range sb.ninodes.toNat).all fun i =>
    let dn := dinode image sb (i : Int)
    if dn.typeZ == 0 then true else inodeDurableValid image sb dn

end Xv6.Fs
