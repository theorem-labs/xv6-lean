import Xv6.Fs.DirectoryDefs

namespace Xv6.Fs

/-- The five fields of the original fs_dir_ok, including the actual finite map. -/
structure DirectoryOK (image : Blocks) (sb : Superblock) (inum : Int) (dn : Dinode) : Prop where
  gran : 16 ∣ dn.sizeZ
  ent : ∀ k : Nat, k < dirNrec dn.sizeZ → DirLive (dataOf image dn) k →
    (0 < ((dirInum (dataOf image dn) k).toNat : Int) ∧
      ((dirInum (dataOf image dn) k).toNat : Int) < sb.ninodes) ∧
      (dinode image sb (dirInum (dataOf image dn) k).toNat).typeZ ≠ 0
  unique : DirNamesUnique (dataOf image dn) (dirNrec dn.sizeZ)
  dot : (dirView (dataOf image dn) (dirNrec dn.sizeZ))[dotName]? = some inum
  dotdot : ∃ value, (dirView (dataOf image dn) (dirNrec dn.sizeZ))[dotdotName]? = some value

end Xv6.Fs
