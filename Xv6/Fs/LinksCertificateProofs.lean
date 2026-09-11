import Xv6.Fs.LinksProofs
import Xv6.Fs.DirectoryCertificateProofs

namespace Xv6.Fs

theorem allTickets_eq_directories image sb : allTickets image sb =
    (directoryInodes image sb).flatMap (fun z => dirTickets image z (dinode image sb z)) := by
  have helper (xs : List Nat) :
      (xs.map (fun (i : Nat) => dirTicketsAt image sb (i : Int))).flatten =
      ((xs.map Int.ofNat).filter (fun i => (dinode image sb i).typeZ == 1)).flatMap
        (fun i => dirTickets image i (dinode image sb i)) := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      by_cases directory : (dinode image sb (i : Int)).typeZ = 1
      · simpa [dirTicketsAt, directory] using
          congrArg (dirTickets image (i : Int) (dinode image sb (i : Int)) ++ ·) ih
      · simpa [dirTicketsAt, directory] using ih
  exact helper _

theorem dirTickets_of_data_eq image self dn data (eq : dataOf image dn = data) :
    dirTickets image self dn = (List.range (dirNrec dn.sizeZ)).filterMap (fun k =>
      if dirLiveb data k && !(((dirInum data k).toNat : Int) == self)
      then some ((dirInum data k).toNat : Int) else none) := by
  unfold dirTickets recTicket
  simp only [eq]

theorem linksValid_of_tickets image sb tickets (eq : allTickets image sb = tickets)
    (checked : (List.range sb.ninodes.toNat).all (fun i =>
      let z : Int := i
      let dn := dinode image sb z
      decide ((tickCount tickets z : Int) ≤ dn.nlinkZ) &&
      (if dn.typeZ == 1 then tickCount tickets z == 0 && dn.nlinkZ == 1 && z == 1 else true)) = true) :
    linksValid image sb = true := by
  unfold linksValid
  rw [eq]
  exact checked

end Xv6.Fs
