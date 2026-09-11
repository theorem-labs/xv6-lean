import Xv6.Fs.LinksDefs
import Xv6.Fs.DirectoryProofs

namespace Xv6.Fs

theorem recTicket_some image self dn k t : recTicket image self dn k = some t ↔
    DirLive (dataOf image dn) k ∧ ((dirInum (dataOf image dn) k).toNat : Int) ≠ self ∧
    ((dirInum (dataOf image dn) k).toNat : Int) = t := by
  simp only [recTicket]
  split
  · rename_i guard
    have g := (Bool.and_eq_true _ _).mp guard
    simp only [Option.some.injEq]
    exact ⟨fun eq => ⟨(dirLiveb_true _ _).mp g.1,
      beq_eq_false_iff_ne.mp (by simpa only [Bool.not_eq_true'] using g.2), eq⟩, fun h => h.2.2⟩
  · rename_i guard
    simp only [reduceCtorEq, false_iff]
    rintro ⟨live, different, _⟩
    apply guard
    rw [(dirLiveb_true _ _).mpr live, beq_eq_false_iff_ne.mpr different]
    rfl

theorem allTickets_range image sb t (valid : dirsValid image sb = true)
    (member : t ∈ allTickets image sb) : 0 < t ∧ t < sb.ninodes := by
  simp only [allTickets, List.mem_flatten, List.mem_map] at member
  obtain ⟨tickets, ⟨i, hi, rfl⟩, ht⟩ := member
  have bound := List.mem_range.mp hi
  unfold dirTicketsAt at ht
  dsimp only at ht
  split at ht
  · rename_i directory
    obtain ⟨k, hk, ticket⟩ := List.mem_filterMap.mp ht
    have record := (recTicket_some _ _ _ _ _).mp ticket
    have ok := dirsValid_spec image sb valid (i : Int) ⟨by omega, by omega⟩
      (beq_iff_eq.mp directory)
    have h := (ok.ent k (List.mem_range.mp hk) record.1).1
    simpa only [record.2.2] using h
  · contradiction

theorem tickCount_zero tickets z (absent : ∀ t ∈ tickets, t ≠ z) : tickCount tickets z = 0 := by
  unfold tickCount
  have empty : tickets.filter (fun t => t == z) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    intro eq
    exact absent t ht (beq_iff_eq.mp eq)
  rw [empty]
  rfl

theorem linkCount_out image sb z (valid : dirsValid image sb = true)
    (outside : ¬ (0 < z ∧ z < sb.ninodes)) : linkCount image sb z = 0 := by
  apply tickCount_zero
  intro t ht eq
  subst t
  exact outside (allTickets_range image sb z valid ht)

theorem linksValid_at image sb z (valid : linksValid image sb = true)
    (bound : 0 ≤ z ∧ z < sb.ninodes) :
    (linkCount image sb z : Int) ≤ (dinode image sb z).nlinkZ ∧
    ((dinode image sb z).typeZ = 1 → linkCount image sb z = 0 ∧
      (dinode image sb z).nlinkZ = 1 ∧ z = 1) := by
  have h := List.all_eq_true.mp valid z.toNat (List.mem_range.mpr (by omega))
  have cast : (z.toNat : Int) = z := Int.toNat_of_nonneg bound.1
  dsimp only at h
  rw [cast] at h
  have parts := (Bool.and_eq_true _ _).mp h
  refine ⟨of_decide_eq_true parts.1, ?_⟩
  intro directory
  have d := parts.2
  rw [directory] at d
  simpa only [BEq.rfl, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, and_assoc,
    linkCount] using d

/-- Duplicate records each contribute a ticket; names and uniqueness are irrelevant here. -/
private def ticketRecord : Dinode := ⟨1, 0, 0, 1, 32, [47]⟩
private def ticketImage (target : BitVec 16) : Blocks := fun _ =>
  direntBytes ⟨target, [65] ++ List.replicate 13 0⟩ ++
  direntBytes ⟨target, [66] ++ List.replicate 13 0⟩

theorem ticket_self_exempt_any_name : dirTickets (ticketImage 1) 1 ticketRecord = [] := by decide

theorem ticket_free_garbage_exempt : dirTickets (ticketImage 0) 1 ticketRecord = [] := by decide

theorem ticket_duplicates_preserved : dirTickets (ticketImage 2) 1 ticketRecord = [2, 2] := by decide

theorem ticket_multiplicity_count : tickCount [2, 2, 3] 2 = 2 := by decide

theorem links_negative_count_vacuous image sb (negative : sb.ninodes ≤ 0) : linksValid image sb = true := by
  have zero : sb.ninodes.toNat = 0 := by omega
  simp only [linksValid, zero, List.range_zero, List.all_nil]

end Xv6.Fs

open Lean Elab Command in
run_cmd do
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs.") then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
