import Xv6.Fs.InodeValidityProofs

/-! Factor W3 into independently certified inode and indirect-entry inputs.
This module contains no concrete filesystem image. -/
namespace Xv6.Fs

/-- The same W3 Boolean expression with its repeated indirect reader factored out. -/
def inodeInputValid (sb : Superblock) (dn : Dinode) (entries : List Int) : Bool :=
  let nb := nblk dn.sizeZ
  let ib := dn.addrZ 12
  (dn.typeZ == 1 || dn.typeZ == 2 || dn.typeZ == 3) &&
  decide (1 ≤ dn.nlinkZ) && decide (dn.sizeZ ≤ 268 * 1024) &&
  (List.range 12).all (fun k =>
    if (k : Int) < nb then addrValid sb (dn.addrZ k) else dn.addrZ k == 0) &&
  (if nb ≤ 12 then ib == 0 else addrValid sb ib) &&
  (List.range 256).all (fun j =>
    if (j : Int) < nb - 12 then addrValid sb (entries[j]?.getD 0)
    else entries[j]?.getD 0 == 0)

theorem inodeValid_eq_inputValid (image : Blocks) (sb : Superblock) (dn : Dinode) :
    inodeValid image sb dn = inodeInputValid sb dn (indirectEntries image dn) := rfl

/-- Each external literal requires both a record equality and an indirect-reader
 equality. This theorem does not accept a replacement for an unchecked input. -/
theorem inodeValid_of_certified_inputs (image : Blocks) (sb : Superblock) (inum : Int)
    (record : Dinode) (entries : List Int)
    (record_eq : dinode image sb inum = record)
    (entries_eq : indirectEntries image record = entries)
    (checked : inodeInputValid sb record entries = true) :
    inodeValid image sb (dinode image sb inum) = true := by
  rw [record_eq, inodeValid_eq_inputValid, entries_eq]
  exact checked

/-- Replacing the advertised sweep by its exact live subset preserves W3's
intentional skip of type-zero records; no other filesystem clause is inferred. -/
theorem inodesValid_of_live (image : Blocks) (sb : Superblock)
    (checked : ∀ z ∈ liveInodes image sb, inodeValid image sb (dinode image sb z) = true) :
    inodesValid image sb = true := by
  unfold inodesValid
  apply List.all_eq_true.mpr
  intro i hi
  have hb := List.mem_range.mp hi
  dsimp only
  split
  · rfl
  · rename_i live
    apply checked
    apply (liveInodes_mem image sb (i : Int)).mpr
    exact ⟨⟨by omega, by omega⟩, by simpa using live⟩

end Xv6.Fs
