import Xv6.Fs.LinksDefs

namespace Xv6.Fs

/-- Separate additive source sweep, FsImg.v3337: exact counts for live non-directories. -/
def linksEqual (image : Blocks) (sb : Superblock) : Bool :=
  let tickets := allTickets image sb
  (List.range sb.ninodes.toNat).all fun i =>
    let z : Int := i
    let dn := dinode image sb z
    if dn.typeZ == 0 || dn.typeZ == 1 then true
    else dn.nlinkZ == (tickCount tickets z : Int)

/-- Separate source fs_root_no_self, including its lazy branch structure. -/
def rootNoSelf (image : Blocks) (sb : Superblock) : Bool :=
  let dn := dinode image sb 1
  let data := dataOf image dn
  (List.range (dirNrec dn.sizeZ)).all fun k =>
    let i := dirInum data k
    if i == 0 then true
    else if (i.toNat : Int) == 1 then
      let name := dirBname data k
      if name == dotName then true else name == dotdotName
    else true

end Xv6.Fs
