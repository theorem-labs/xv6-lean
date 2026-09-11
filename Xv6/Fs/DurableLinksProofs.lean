import Xv6.Fs.DurableLinksDefs
import Xv6.Fs.LinksProofs

namespace Xv6.Fs

theorem linksEqual_at image sb z (valid : linksEqual image sb = true)
    (bound : 0 ≤ z ∧ z < sb.ninodes) (live : (dinode image sb z).typeZ ≠ 0)
    (non_directory : (dinode image sb z).typeZ ≠ 1) :
    (dinode image sb z).nlinkZ = (linkCount image sb z : Int) := by
  have h := List.all_eq_true.mp valid z.toNat (List.mem_range.mpr (by omega))
  have cast : (z.toNat : Int) = z := Int.toNat_of_nonneg bound.1
  dsimp only at h
  rw [cast] at h
  simpa only [beq_eq_false_iff_ne.mpr live, beq_eq_false_iff_ne.mpr non_directory,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, linkCount] using h

theorem rootNoSelf_at image sb k (valid : rootNoSelf image sb = true)
    (bound : k < dirNrec (dinode image sb 1).sizeZ)
    (live : DirLive (dataOf image (dinode image sb 1)) k)
    (self : ((dirInum (dataOf image (dinode image sb 1)) k).toNat : Int) = 1) :
    dirBname (dataOf image (dinode image sb 1)) k = dotName ∨
    dirBname (dataOf image (dinode image sb 1)) k = dotdotName := by
  have h := List.all_eq_true.mp valid k (List.mem_range.mpr bound)
  dsimp only at h
  rw [beq_eq_false_iff_ne.mpr live, self] at h
  simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl] at h
  split at h
  · rename_i dot
    exact Or.inl (beq_iff_eq.mp dot)
  · exact Or.inr (beq_iff_eq.mp h)

theorem linksEqual_of_tickets image sb tickets (eq : allTickets image sb = tickets)
    (checked : (List.range sb.ninodes.toNat).all (fun i =>
      let z : Int := i
      let dn := dinode image sb z
      if dn.typeZ == 0 || dn.typeZ == 1 then true
      else dn.nlinkZ == (tickCount tickets z : Int)) = true) : linksEqual image sb = true := by
  unfold linksEqual
  rw [eq]
  exact checked

theorem rootNoSelf_of_data_eq image sb dn data (record : dinode image sb 1 = dn)
    (data_eq : dataOf image dn = data)
    (checked : (List.range (dirNrec dn.sizeZ)).all (fun k =>
      let i := dirInum data k
      if i == 0 then true else if (i.toNat : Int) == 1 then
        let name := dirBname data k
        if name == dotName then true else name == dotdotName
      else true) = true) : rootNoSelf image sb = true := by
  unfold rootNoSelf
  rw [record]
  dsimp only
  rw [data_eq]
  exact checked

end Xv6.Fs
