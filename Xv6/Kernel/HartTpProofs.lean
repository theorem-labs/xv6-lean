import Xv6.Kernel.HartTpPure
import MachCSL.Logic.RegisterSpec

namespace Xv6.Kernel.HartTp
open Iris Iris.BI Iris.ProofMode MachCSL.Machine MachCSL.Logic
open Iris.BI.BigSepL

variable {GF : BundledGFunctors} (capacity : Registers.Capacity GF)

theorem lookup_split (registerName : GName) (values : GprFile) (index : Index) :
    iprop(file capacity registerName values ⊣⊢
      pointsto capacity registerName index (.own 1) (values index) ∗
      remainder capacity registerName values index) := by
  have perm := List.perm_cons_erase (all_indices index)
  rw [unique_indices.erase_eq_filter] at perm
  unfold file remainder
  exact (bigSepL_perm perm).trans bigSepL_cons

theorem remainder_set (registerName : GName) (values : GprFile) (index : Index) (value : Word) :
    remainder capacity registerName (set values index value) index =
      remainder capacity registerName values index := by
  unfold remainder
  apply bigSepL_eq
  intro k other member
  have filtered := List.mem_filter.mp (List.mem_of_getElem? member)
  have different : other ≠ index := by simpa using filtered.2
  rw [set_other values index other value different]

theorem replace (registerName : GName) (values : GprFile) (index : Index) (value : Word) :
    iprop(⊢ pointsto capacity registerName index (.own 1) value -∗
      remainder capacity registerName values index -∗
      file capacity registerName (set values index value)) := by
  rw [(lookup_split capacity registerName (set values index value) index).to_eq,
    set_same, remainder_set]
  iintro Hcell Hrest
  iframe

theorem lookup (registerName : GName) (values : GprFile) (index : Index) :
    iprop(⊢ file capacity registerName values -∗
      pointsto capacity registerName index (.own 1) (values index) ∗
      (pointsto capacity registerName index (.own 1) (values index) -∗
        file capacity registerName values)) := by
  iintro Hfile
  ihave ⟨Hcell, Hrest⟩ := (lookup_split capacity registerName values index).1 $$ Hfile
  iframe Hcell
  iintro Hcell
  rw [(lookup_split capacity registerName values index).to_eq]
  iframe

theorem update (registerName : GName) (values : GprFile) (index : Index) :
    iprop(⊢ file capacity registerName values -∗
      pointsto capacity registerName index (.own 1) (values index) ∗
      (∀ value, pointsto capacity registerName index (.own 1) value -∗
        file capacity registerName (set values index value))) := by
  iintro Hfile
  ihave ⟨Hcell, Hrest⟩ := (lookup_split capacity registerName values index).1 $$ Hfile
  iframe Hcell
  iintro %value Hcell
  iapply replace capacity registerName values index value $$ Hcell Hrest

theorem zero_value (registerName : GName) (values : GprFile) :
    iprop(⊢ file capacity registerName values -∗ ⌜values 0#5 = 0#64⌝) := by
  iintro Hfile
  ihave ⟨Hzero, _⟩ := (lookup_split capacity registerName values 0#5).1 $$ Hfile
  ieval (simp [pointsto, physical]) at Hzero
  iexact Hzero

theorem pinned_lookup (era : Era.Record) (cpu : CPU) (values : GprFile) (index : Index) :
    iprop(⊢ pinnedFile capacity era cpu values -∗
      pointsto capacity (era.registers cpu) index (.own 1) (rget cpu values index) ∗
      (pointsto capacity (era.registers cpu) index (.own 1) (rget cpu values index) -∗
        pinnedFile capacity era cpu values)) :=
  lookup capacity (era.registers cpu) (pin cpu values) index

theorem pinned_update (era : Era.Record) (cpu : CPU) (values : GprFile) (index : Index)
    (different : index ≠ tp) :
    iprop(⊢ pinnedFile capacity era cpu values -∗
      pointsto capacity (era.registers cpu) index (.own 1) (rget cpu values index) ∗
      (∀ value, pointsto capacity (era.registers cpu) index (.own 1) value -∗
        pinnedFile capacity era cpu (set values index value))) := by
  unfold pinnedFile rget
  have law := update capacity (era.registers cpu) (pin cpu values) index
  simpa only [pin_set cpu values index _ different] using law

theorem tp_accessor (era : Era.Record) (cpu : CPU) (values : GprFile) :
    iprop(⊢ pinnedFile capacity era cpu values -∗
      Registers.regPointsto capacity (era.registers cpu) .x4 (.own 1) (hartWord cpu) ∗
      (Registers.regPointsto capacity (era.registers cpu) .x4 (.own 1) (hartWord cpu) -∗
        pinnedFile capacity era cpu values)) := by
  have law := pinned_lookup capacity era cpu values tp
  rw [pinned_tp] at law
  exact law

theorem actual_tp (registerSpec : Registers.RegisterSpec capacity)
    (era : Era.Record) (cpu : CPU) (values : GprFile) (registers : RegisterFile) :
    iprop(⊢ Registers.regInterpAt capacity (era.registers cpu) registers -∗
      pinnedFile capacity era cpu values -∗ ⌜registers .x4 = hartWord cpu⌝) := by
  iintro Hinterp Hfile
  ihave ⟨Htp, _⟩ := tp_accessor capacity era cpu values $$ Hfile
  iapply registerSpec.read (era.registers cpu) registers .x4 (.own 1) (hartWord cpu) $$ Hinterp Htp

theorem actual (registerSpec : Registers.RegisterSpec capacity) : Spec capacity where
  lookupSplit := lookup_split capacity
  replace := replace capacity
  lookup := lookup capacity
  update := update capacity
  zeroValue := zero_value capacity
  pinnedLookup := pinned_lookup capacity
  pinnedUpdate := pinned_update capacity
  tpAccessor := tp_accessor capacity
  actualTp := actual_tp capacity registerSpec

end Xv6.Kernel.HartTp
