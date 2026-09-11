import Xv6.Fs.DirentDefs
import Xv6.Fs.InodeValidityDefs

/-! Exact W6/W7/W8 from FsImg.v:1919–2274. -/
namespace Xv6.Fs

def uniqStep (data : FileData) (k : Nat) (names : NameSet) : Option NameSet :=
  if dirLiveb data k then
    if dirBname data k ∈ names then none else some (names.insert (dirBname data k))
  else some names

def dirUniqb (data : FileData) : Nat → Option NameSet
  | 0 => some ∅
  | n + 1 => match dirUniqb data n with
    | none => none
    | some names => uniqStep data n names

def dirValid (image : Blocks) (sb : Superblock) (self : Int) (dn : Dinode) : Bool :=
  let data := dataOf image dn
  let nrec := dirNrec dn.sizeZ
  (dn.sizeZ % 16 == 0) &&
  (List.range nrec).all (fun k => !dirLiveb data k ||
    (let inum : Int := (dirInum data k).toNat
     decide (0 < inum) && decide (inum < sb.ninodes) &&
       !((dinode image sb inum).typeZ == 0))) &&
  (dirUniqb data nrec).isSome &&
  (match dirFirst data nrec dotName with
    | some k => ((dirInum data k).toNat : Int) == self
    | none => false) &&
  (dirFirst data nrec dotdotName).isSome

def dirsValid (image : Blocks) (sb : Superblock) : Bool :=
  (List.range sb.ninodes.toNat).all fun (i : Nat) =>
    let dn := dinode image sb (i : Int)
    if dn.typeZ == 1 then dirValid image sb (i : Int) dn else true

def dotsValid (image : Blocks) (self : Int) (dn : Dinode) : Bool :=
  let data := dataOf image dn
  let nrec := dirNrec dn.sizeZ
  decide (2 ≤ nrec) && dirLiveb data 0 &&
  (((dirInum data 0).toNat : Int) == self) && (dirBname data 0 == dotName) &&
  dirLiveb data 1 && (dirBname data 1 == dotdotName)

def dotsAll (image : Blocks) (sb : Superblock) : Bool :=
  (List.range sb.ninodes.toNat).all fun (i : Nat) =>
    let dn := dinode image sb (i : Int)
    if dn.typeZ == 1 then dotsValid image (i : Int) dn else true

def rootValid (image : Blocks) (sb : Superblock) : Bool :=
  let dn := dinode image sb 1
  let data := dataOf image dn
  (dn.typeZ == 1) &&
  (match dirFirst data (dirNrec dn.sizeZ) dotdotName with
    | some k => ((dirInum data k).toNat : Int) == 1
    | none => false)

end Xv6.Fs
