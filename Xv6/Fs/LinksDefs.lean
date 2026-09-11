import Xv6.Fs.DirectoryDefs

/-! Exact FsImg.v W9 ticket order and link-count checker (2315–2444).
Self exemption tests inode identity; it does not inspect the name. -/
namespace Xv6.Fs

def recTicket (image : Blocks) (self : Int) (dn : Dinode) (k : Nat) : Option Int :=
  let data := dataOf image dn
  if dirLiveb data k && !(((dirInum data k).toNat : Int) == self)
  then some (dirInum data k).toNat else none

def dirTickets (image : Blocks) (self : Int) (dn : Dinode) : List Int :=
  (List.range (dirNrec dn.sizeZ)).filterMap (recTicket image self dn)

def dirTicketsAt (image : Blocks) (sb : Superblock) (z : Int) : List Int :=
  let dn := dinode image sb z
  if dn.typeZ == 1 then dirTickets image z dn else []

def allTickets (image : Blocks) (sb : Superblock) : List Int :=
  ((List.range sb.ninodes.toNat).map fun (i : Nat) => dirTicketsAt image sb (i : Int)).flatten

def tickCount (tickets : List Int) (z : Int) : Nat :=
  (tickets.filter fun t => t == z).length

def linkCount (image : Blocks) (sb : Superblock) (z : Int) : Nat :=
  tickCount (allTickets image sb) z

def linksValid (image : Blocks) (sb : Superblock) : Bool :=
  let tickets := allTickets image sb
  (List.range sb.ninodes.toNat).all fun i =>
    let z : Int := i
    let dn := dinode image sb z
    decide ((tickCount tickets z : Int) ≤ dn.nlinkZ) &&
    (if dn.typeZ == 1 then tickCount tickets z == 0 && dn.nlinkZ == 1 && z == 1 else true)

end Xv6.Fs
