import Xv6.Fs.DurableInodeDefs
import Xv6.Fs.InodeValidityProofs

set_option maxRecDepth 4096
namespace Xv6.Fs

theorem inodeDurableValid_ok image sb dn (valid : inodeDurableValid image sb dn = true) :
    InodeDurableOK image sb dn := by
  simp only [inodeDurableValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at valid
  obtain ⟨⟨⟨⟨type, size⟩, direct⟩, ind⟩, entries⟩ := valid
  refine ⟨(by simpa only [or_assoc] using type), size, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk lt
    have h := direct k hk
    rw [if_pos lt] at h
    exact (addrValid_iff sb _).mp h
  · intro k hk nz
    have h := direct k hk
    split at h
    · exact (addrValid_iff sb _).mp h
    · simp only [Bool.or_eq_true, beq_iff_eq] at h
      exact (addrValid_iff sb _).mp (h.resolve_left nz)
  · intro nz
    split at ind
    · simp only [Bool.or_eq_true, beq_iff_eq] at ind
      exact (addrValid_iff sb _).mp (ind.resolve_left nz)
    · exact (addrValid_iff sb _).mp ind
  · intro lt
    rw [if_neg (by omega)] at ind
    exact (addrValid_iff sb _).mp ind
  · intro j hj lt
    have h := entries j hj
    rw [if_pos lt] at h
    exact (addrValid_iff sb _).mp h
  · intro j hj nz
    have h := entries j hj
    split at h
    · exact (addrValid_iff sb _).mp h
    · simp only [Bool.or_eq_true, beq_iff_eq] at h
      exact (addrValid_iff sb _).mp (h.resolve_left nz)

theorem inodeDurableValid_of_ok image sb dn (ok : InodeDurableOK image sb dn) :
    inodeDurableValid image sb dn = true := by
  simp only [inodeDurableValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨(by simpa only [or_assoc] using ok.type), ok.size⟩, ?_⟩, ?_⟩, ?_⟩
  · intro k hk
    split
    · exact (addrValid_iff sb _).mpr (ok.direct k hk ‹_›)
    · by_cases zero : dn.addrZ k = 0
      · simp only [zero, BEq.rfl, Bool.true_or]
      · exact (Bool.or_eq_true _ _).mpr (Or.inr ((addrValid_iff sb _).mpr (ok.direct_ok k hk zero)))
  · split
    · by_cases zero : dn.addrZ 12 = 0
      · simp only [zero, BEq.rfl, Bool.true_or]
      · exact (Bool.or_eq_true _ _).mpr (Or.inr ((addrValid_iff sb _).mpr (ok.ind_ok zero)))
    · exact (addrValid_iff sb _).mpr (ok.ind (by omega))
  · intro j hj
    split
    · exact (addrValid_iff sb _).mpr (ok.ent j hj ‹_›)
    · by_cases zero : (indirectEntries image dn)[j]?.getD 0 = 0
      · simp only [zero, BEq.rfl, Bool.true_or]
      · exact (Bool.or_eq_true _ _).mpr (Or.inr ((addrValid_iff sb _).mpr (ok.ent_ok j hj zero)))

theorem inodeDurableValid_iff image sb dn :
    inodeDurableValid image sb dn = true ↔ InodeDurableOK image sb dn :=
  ⟨inodeDurableValid_ok image sb dn, inodeDurableValid_of_ok image sb dn⟩

theorem InodeOK.durable image sb dn (ok : InodeOK image sb dn) : InodeDurableOK image sb dn := by
  refine ⟨ok.type, ok.size, ok.direct, ?_, ?_, ok.ind, ok.ent, ?_⟩
  · intro k hk nz
    by_cases lt : (k : Int) < nblk dn.sizeZ
    · exact ok.direct k hk lt
    · exact False.elim (nz (ok.direct_zero k hk (by omega)))
  · intro nz
    by_cases lt : 12 < nblk dn.sizeZ
    · exact ok.ind lt
    · exact False.elim (nz (ok.ind_zero (by omega)))
  · intro j hj nz
    by_cases lt : (j : Int) < nblk dn.sizeZ - 12
    · exact ok.ent j hj lt
    · exact False.elim (nz (ok.ent_zero j hj (by omega)))

theorem inodeValid_durable image sb dn (valid : inodeValid image sb dn = true) :
    inodeDurableValid image sb dn = true :=
  inodeDurableValid_of_ok image sb dn ((inodeValid_ok image sb dn valid).durable image sb dn)

theorem inodesDurableValid_spec image sb i (valid : inodesDurableValid image sb = true)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (live : (dinode image sb i).typeZ ≠ 0) :
    InodeDurableOK image sb (dinode image sb i) := by
  have h := List.all_eq_true.mp valid i.toNat (List.mem_range.mpr (by omega))
  have cast : (i.toNat : Int) = i := Int.toNat_of_nonneg bound.1
  apply inodeDurableValid_ok
  simpa only [cast, beq_eq_false_iff_ne.mpr live, Bool.false_eq_true, ↓reduceIte] using h

theorem inodesValid_durable image sb (valid : inodesValid image sb = true) :
    inodesDurableValid image sb = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have h := List.all_eq_true.mp valid i hi
  dsimp only at h ⊢
  by_cases free : (dinode image sb (i : Int)).typeZ = 0
  · simp only [free, BEq.rfl, ↓reduceIte]
  · simp only [beq_eq_false_iff_ne.mpr free, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact inodeValid_durable image sb _ h

/-- Source size-update rule: allocation is unchanged; coverage is owed at the new size. -/
theorem InodeDurableOK.move_size image sb dn dn' (ok : InodeDurableOK image sb dn)
    (type : dn'.type = dn.type) (addrs : dn'.addrs = dn.addrs)
    (capacity : dn'.sizeZ ≤ 268 * 1024)
    (covers : ∀ k : Nat, k < 268 → (k : Int) < nblk dn'.sizeZ → blockAddress image dn k ≠ 0) :
    InodeDurableOK image sb dn' := by
  have address (k : Nat) : dn'.addrZ k = dn.addrZ k := by simp only [Dinode.addrZ, addrs]
  have entries : indirectEntries image dn' = indirectEntries image dn := by
    simp only [indirectEntries, addrs]
  refine ⟨?_, capacity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Dinode.typeZ, type] using ok.type
  · intro k hk lt
    rw [address]
    apply ok.direct_ok k hk
    have nz := covers k (by omega) lt
    simpa only [blockAddress, hk, ↓reduceIte, Dinode.addrZ] using nz
  · intro k hk nz
    rw [address] at nz ⊢
    exact ok.direct_ok k hk nz
  · intro nz
    rw [address] at nz ⊢
    exact ok.ind_ok nz
  · intro lt
    rw [address]
    apply ok.ind_ok
    intro zero
    have nz := covers 12 (by omega) lt
    have empty : indirectEntries image dn = List.replicate 256 0 := by
      unfold indirectEntries
      change (if dn.addrZ 12 == 0 then _ else _) = _
      rw [zero]
      rfl
    apply nz
    simp only [blockAddress, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, empty]
    rfl
  · intro j hj lt
    rw [entries]
    apply ok.ent_ok j hj
    have nz := covers (12 + j) (by omega) (by omega)
    simpa only [blockAddress, show ¬ 12 + j < 12 by omega, ↓reduceIte,
      Nat.add_sub_cancel_left] using nz
  · intro j hj nz
    rw [entries] at nz ⊢
    exact ok.ent_ok j hj nz

private def durableExampleSb : Superblock := ⟨0, 100, 53, 20, 31, 2, 33, 46⟩
private def orphanRecord : Dinode := ⟨2, 0, 0, 0, 0, List.replicate 13 0⟩
private def beyondRecord : Dinode := ⟨2, 0, 0, 1, 0, [47] ++ List.replicate 12 0⟩

theorem durable_zero_link_orphan : inodeDurableValid (fun _ => []) durableExampleSb orphanRecord = true := by decide

theorem initial_zero_link_orphan_rejected : inodeValid (fun _ => []) durableExampleSb orphanRecord = false := by decide

theorem durable_beyond_size_allocation : inodeDurableValid (fun _ => []) durableExampleSb beyondRecord = true := by decide

theorem initial_beyond_size_allocation_rejected : inodeValid (fun _ => []) durableExampleSb beyondRecord = false := by decide

theorem durable_beyond_size_metadata_rejected :
    inodeDurableValid (fun _ => []) durableExampleSb { beyondRecord with addrs := [46] } = false := by decide

end Xv6.Fs

open Lean Elab Command in
run_cmd do
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs.") then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
