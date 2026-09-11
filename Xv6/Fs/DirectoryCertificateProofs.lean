import Xv6.Fs.DirectoryProofs

/-! Pure assembly lemmas keep actual images behind checked reader equalities. -/
namespace Xv6.Fs

def directoryInodes (image : Blocks) (sb : Superblock) : List Int :=
  ((List.range sb.ninodes.toNat).map Int.ofNat).filter
    (fun i => (dinode image sb i).typeZ == 1)

theorem directoryInodes_mem image sb i : i ∈ directoryInodes image sb ↔
    (0 ≤ i ∧ i < sb.ninodes) ∧ (dinode image sb i).typeZ = 1 := by
  simp only [directoryInodes, List.mem_filter, List.mem_map, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨⟨n, bound, rfl⟩, directory⟩
    refine ⟨?_, directory⟩
    change 0 ≤ (n : Int) ∧ (n : Int) < sb.ninodes
    omega
  · rintro ⟨bound, directory⟩
    exact ⟨⟨i.toNat, by omega, Int.toNat_of_nonneg bound.1⟩, directory⟩

theorem dirsValid_of_directories image sb
    (checked : ∀ i ∈ directoryInodes image sb, dirValid image sb i (dinode image sb i) = true) :
    dirsValid image sb = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have bound := List.mem_range.mp hi
  dsimp only
  split
  · rename_i directory
    exact checked (i : Int) ((directoryInodes_mem image sb _).mpr
      ⟨⟨by omega, by omega⟩, beq_iff_eq.mp directory⟩)
  · rfl

theorem dotsAll_of_directories image sb
    (checked : ∀ i ∈ directoryInodes image sb, dotsValid image i (dinode image sb i) = true) :
    dotsAll image sb = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have bound := List.mem_range.mp hi
  dsimp only
  split
  · rename_i directory
    exact checked (i : Int) ((directoryInodes_mem image sb _).mpr
      ⟨⟨by omega, by omega⟩, beq_iff_eq.mp directory⟩)
  · rfl

/-- A direct one-block record, with no indirect block, names no other data. -/
theorem dataOf_one_block image dn address (addrs : dn.addrs = BitVec.ofInt 32 address :: List.replicate 12 0)
    (address_ok : 0 < address ∧ address < 2 ^ 32) (k : Nat) :
    dataOf image dn k = if k = 0 then image address else List.replicate 1024 0 := by
  have cast : ((BitVec.ofInt 32 address).toNat : Int) = address := by
    rw [BitVec.toNat_ofInt]
    omega
  have last : dn.addrs[12]?.getD 0 = 0 := by
    rw [addrs]
    rfl
  have entries : indirectEntries image dn = List.replicate 256 0 := by
    unfold indirectEntries
    rw [last]
    rfl
  have addr : blockAddress image dn k = if k = 0 then address else 0 := by
    unfold blockAddress
    cases k with
    | zero =>
      simp only [Nat.reduceLT, ↓reduceIte, addrs, List.getElem?_cons_zero, Option.getD_some]
      exact cast
    | succ j =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      split
      · rw [addrs]
        simp only [List.getElem?_cons_succ, List.getElem?_replicate]
        split <;> rfl
      · rw [entries]
        simp only [List.getElem?_replicate]
        split <;> rfl
  rw [dataOf_address, addr]
  by_cases zero : k = 0
  · rw [if_pos zero, if_pos zero]
    have nz : (address == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    rw [nz]
    rfl
  · rw [if_neg zero, if_neg zero]
    rfl

theorem directoryOK_of_data_eq image sb inum dn data (data_eq : dataOf image dn = data)
    (gran : 16 ∣ dn.sizeZ)
    (entries : ∀ k < dirNrec dn.sizeZ, DirLive data k →
      (0 < ((dirInum data k).toNat : Int) ∧ ((dirInum data k).toNat : Int) < sb.ninodes) ∧
      (dinode image sb (dirInum data k).toNat).typeZ ≠ 0)
    (unique : DirNamesUnique data (dirNrec dn.sizeZ))
    (dot : (dirView data (dirNrec dn.sizeZ))[dotName]? = some inum)
    (dotdot : ∃ value, (dirView data (dirNrec dn.sizeZ))[dotdotName]? = some value) :
    DirectoryOK image sb inum dn := by
  constructor
  · exact gran
  · simpa only [data_eq] using entries
  · simpa only [data_eq] using unique
  · simpa only [data_eq] using dot
  · simpa only [data_eq] using dotdot

theorem dotsValid_of_data_eq image inum dn data (data_eq : dataOf image dn = data)
    (checked : (decide (2 ≤ dirNrec dn.sizeZ) && dirLiveb data 0 &&
      (((dirInum data 0).toNat : Int) == inum) && (dirBname data 0 == dotName) &&
      dirLiveb data 1 && (dirBname data 1 == dotdotName)) = true) :
    dotsValid image inum dn = true := by
  unfold dotsValid
  simpa only [data_eq] using checked

theorem rootValid_of_data_eq image sb dn data (record_eq : dinode image sb 1 = dn)
    (data_eq : dataOf image dn = data) (directory : dn.typeZ = 1)
    (dotdot : (dirView data (dirNrec dn.sizeZ))[dotdotName]? = some 1) : rootValid image sb = true := by
  unfold rootValid
  rw [record_eq]
  dsimp only
  rw [data_eq, directory]
  simp only [BEq.rfl, Bool.true_and]
  obtain ⟨k, first, value⟩ := (dirView_lookup_some _ _ _ _).mp dotdot
  rw [first]
  exact beq_iff_eq.mpr value

end Xv6.Fs
