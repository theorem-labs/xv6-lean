import MachCSL.Logic.RegisterFootprintSpec

namespace MachCSL.Logic.RegisterFootprint
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Registers.Capacity GF)

theorem cells_append γ rs (left right : Footprint) :
    iprop(cells capacity γ rs (left ++ right) ⊣⊢
      cells capacity γ rs left ∗ cells capacity γ rs right) := by
  induction left with
  | nil => simp only [List.nil_append, cells]; exact emp_sep.symm
  | cons entry rest ih =>
    rcases entry with ⟨r, dq⟩
    simp only [List.cons_append, cells]
    rw [ih.to_eq]
    exact sep_assoc.symm

theorem cells_write_other γ rs (footprint : Footprint) r (value : RegisterType r)
    (absent : r ∉ footprint.map Prod.fst) :
    cells capacity γ (Sail.Registers.write rs r value) footprint = cells capacity γ rs footprint := by
  induction footprint with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, dq⟩
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    simp only [cells, Sail.Registers.write_other rs r key value absent.1, ih absent.2]

theorem read_access γ rs (footprint : Footprint) r dq (member : (r, dq) ∈ footprint) :
    iprop(⊢ cells capacity γ rs footprint -∗
      Registers.regPointsto capacity γ r dq (rs r) ∗
      (Registers.regPointsto capacity γ r dq (rs r) -∗ cells capacity γ rs footprint)) := by
  induction footprint with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨key, share⟩
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [cells]
      iintro ⟨Hcell, Hrest⟩
      iframe Hcell
      iintro Hcell
      iframe Hcell Hrest
    · simp only [cells]
      iintro ⟨Hhead, Hrest⟩
      ihave ⟨Hcell, Hrestore⟩ := ih member $$ Hrest
      iframe Hcell
      iintro Hcell
      iframe Hhead
      iapply Hrestore $$ Hcell

theorem write_access γ rs (footprint : Footprint) r
    (unique : Unique footprint) (member : (r, .own 1) ∈ footprint) :
    iprop(⊢ cells capacity γ rs footprint -∗
      Registers.regPointsto capacity γ r (.own 1) (rs r) ∗
      (∀ value : RegisterType r, Registers.regPointsto capacity γ r (.own 1) value -∗
        cells capacity γ (Sail.Registers.write rs r value) footprint)) := by
  induction footprint with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨key, share⟩
    have unique' := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [cells]
      iintro ⟨Hcell, Hrest⟩
      iframe Hcell
      iintro %value Hcell
      rw [Sail.Registers.write_same, cells_write_other capacity γ rs rest r value unique'.1]
      iframe Hcell Hrest
    · have different : r ≠ key := by
        intro same
        apply unique'.1
        exact List.mem_map.mpr ⟨(r, .own 1), member, same⟩
      simp only [cells]
      iintro ⟨Hhead, Hrest⟩
      ihave ⟨Hcell, Hrestore⟩ := ih unique'.2 member $$ Hrest
      iframe Hcell
      iintro %value Hcell
      rw [Sail.Registers.write_other rs r key value different]
      iframe Hhead
      iapply Hrestore $$ %value Hcell

theorem actual : Spec capacity := ⟨read_access capacity, write_access capacity⟩

end MachCSL.Logic.RegisterFootprint
