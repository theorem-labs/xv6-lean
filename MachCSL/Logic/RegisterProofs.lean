import MachCSL.Logic.RegisterSpec

/-! Authority-backed rules for actual generated RISC-V registers. -/
namespace MachCSL.Logic.Registers
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap

/-- Every generated constructor is below the computed terminal constructor index. -/
theorem ctorIdx_lt_count (r : Register) : r.ctorIdx < registerCount := by
  cases r <;> decide

theorem allRegisters_complete (r : Register) : r ∈ allRegisters := by
  apply List.mem_map.mpr
  exact ⟨r.ctorIdx, List.mem_range.mpr (ctorIdx_lt_count r), ofNat_ctorIdx r⟩

theorem registerCount_eq : registerCount = 180 := rfl

theorem allRegisters_length : allRegisters.length = registerCount := by
  simp [allRegisters]

theorem mapRegisters_lookup (rs : Machine.RegisterFile) (keys : List Register) (r : Register) :
    get? (mapRegisters rs keys) r = if r ∈ keys then some (⟨r, rs r⟩ : Value) else none := by
  induction keys with
  | nil => simp [mapRegisters, get?_empty]
  | cons key rest ih =>
    simp only [mapRegisters, get?_insert]
    by_cases eq : key = r
    · subst key
      simp
    · simp [eq, ih, Ne.symm eq]

theorem initialMap_lookup (rs : Machine.RegisterFile) (r : Register) :
    get? (initialMap rs) r = some (⟨r, rs r⟩ : Value) := by
  simp only [initialMap, mapRegisters_lookup, if_pos (allRegisters_complete r)]

theorem initialMap_agree (rs : Machine.RegisterFile) : RegAgree (initialMap rs) rs := by
  intro r dv h
  rw [initialMap_lookup] at h
  exact (Option.some.inj h).symm

theorem regAgree_write {map : RegisterMap Value} {rs : Machine.RegisterFile}
    (agree : RegAgree map rs) (r : Register) (v : RegisterType r) :
    RegAgree (insert map r (⟨r, v⟩ : Value)) (Sail.Registers.write rs r v) := by
  intro key dv lookup
  by_cases eq : r = key
  · subst key
    rw [get?_insert_eq rfl] at lookup
    cases Option.some.inj lookup
    simp
  · rw [get?_insert_ne eq] at lookup
    rw [agree key dv lookup, Sail.Registers.write_other rs r key v eq]

/-- Equality of packed values at the same actual enum key implies typed equality. -/
theorem value_inj (r : Register) (v w : RegisterType r)
    (h : (⟨r, v⟩ : Value) = ⟨r, w⟩) : v = w :=
  eq_of_heq (Sigma.mk.inj h).2

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance regPointsto_timeless γ r dq v : Timeless (regPointsto capacity γ r dq v) := by
  letI := capacity.registers
  unfold regPointsto; infer_instance
instance regPointsto_persistent γ r v : Persistent (regPointsto capacity γ r .discard v) := by
  letI := capacity.registers
  unfold regPointsto; infer_instance
instance regAuth_timeless γ dq map : Timeless (regAuth capacity γ dq map) := by
  letI := capacity.registers
  unfold regAuth; infer_instance
instance regInterpAt_timeless γ rs : Timeless (regInterpAt capacity γ rs) := by
  unfold regInterpAt; infer_instance
instance regPointsto_fractional γ r v :
    Fractional (fun q => regPointsto capacity γ r (.own q) v) := by
  letI := capacity.registers
  unfold regPointsto; infer_instance

theorem regPointsto_halves γ r v :
    iprop(regPointsto capacity γ r (.own 1) v ⊣⊢
      regPointsto capacity γ r (.own (Qp.half 1)) v ∗
      regPointsto capacity γ r (.own (Qp.half 1)) v) := by
  have h := (regPointsto_fractional capacity γ r v).fractional (Qp.half 1) (Qp.half 1)
  simpa only [Qp.half_add_half] using h

theorem regPointsto_agree γ r dq1 dq2 v1 v2 :
    iprop(regPointsto capacity γ r dq1 v1 ∗ regPointsto capacity γ r dq2 v2 ⊢ ⌜v1 = v2⌝) := by
  letI := capacity.registers
  unfold regPointsto
  iintro H
  ihave %eq := ghost_map_elem_agree γ r dq1 dq2 (⟨r, v1⟩ : Value) ⟨r, v2⟩ $$ H
  ipureintro
  exact value_inj r v1 v2 eq

theorem regPointsto_persist γ r dq v :
    iprop(⊢ regPointsto capacity γ r dq v ==∗ regPointsto capacity γ r .discard v) := by
  letI := capacity.registers
  exact ghost_map_elem_persist γ r dq (⟨r, v⟩ : Value)

/-- Exact source `reg_valid_dq`; the full-fraction read rule is a specialization. -/
theorem reg_valid_dq γ rs r dq v :
    iprop(⊢ regInterpAt capacity γ rs -∗ regPointsto capacity γ r dq v -∗ ⌜rs r = v⌝) := by
  letI := capacity.registers
  unfold regInterpAt regAuth regPointsto
  iintro ⟨%map, Ha, %agree⟩ Hr
  ihave %lookup := ghost_map_lookup $$ Ha Hr
  ipureintro
  exact (value_inj r v (rs r) (agree r _ lookup)).symm

theorem reg_valid γ rs r v :
    iprop(⊢ regInterpAt capacity γ rs -∗ regPointsto capacity γ r (.own 1) v -∗ ⌜rs r = v⌝) :=
  reg_valid_dq capacity γ rs r (.own 1) v

/-- Full ownership updates the actual dependent machine register file. -/
theorem reg_update γ rs r v v' :
    iprop(⊢ regInterpAt capacity γ rs -∗ regPointsto capacity γ r (.own 1) v ==∗
      regInterpAt capacity γ (Sail.Registers.write rs r v') ∗
      regPointsto capacity γ r (.own 1) v') := by
  letI := capacity.registers
  unfold regInterpAt regAuth regPointsto
  iintro ⟨%map, Ha, %agree⟩ Hr
  imod ghost_map_update (⟨r, v'⟩ : Value) $$ Ha Hr with ⟨Ha, Hr⟩
  imodintro
  iframe Hr
  iexists insert map r (⟨r, v'⟩ : Value)
  iframe Ha
  ipureintro
  exact regAgree_write agree r v'

/-- Same-valued writes preserve the bridge without requiring a writable cell. -/
theorem reg_interp_set_same γ rs r v (same : rs r = v) :
    iprop(⊢ regInterpAt capacity γ rs -∗ regInterpAt capacity γ (Sail.Registers.write rs r v)) := by
  rw [← same, Sail.Registers.write_current]
  iintro H
  iexact H

/-- The write leaves any disjoint Iris resources available to the caller. -/
theorem reg_update_frame γ rs r v v' (P : IProp GF) :
    iprop(⊢ regInterpAt capacity γ rs ∗ regPointsto capacity γ r (.own 1) v ∗ P ==∗
      regInterpAt capacity γ (Sail.Registers.write rs r v') ∗
      regPointsto capacity γ r (.own 1) v' ∗ P) := by
  iintro ⟨Hi, Hr, HP⟩
  imod reg_update capacity γ rs r v v' $$ Hi Hr with ⟨Hi, Hr⟩
  imodintro
  iframe Hi Hr HP

/-- Allocate the nonempty complete generated-register map for any actual state. -/
theorem reg_alloc (rs : Machine.RegisterFile) :
    iprop(⊢ |==> ∃ γ, regInterpAt capacity γ rs ∗ initialCells capacity γ rs) := by
  letI := capacity.registers
  unfold regInterpAt initialCells regAuth
  imod ghost_map_alloc (initialMap rs) with ⟨%γ, Ha, Hcells⟩
  imodintro
  iexists γ
  iframe Hcells
  iexists initialMap rs
  iframe Ha
  ipureintro
  exact initialMap_agree rs

/-- Every initialized typed register cell is accessible, with its reassembly wand. -/
theorem initialCells_acc γ rs r :
    iprop(⊢ initialCells capacity γ rs -∗
      regPointsto capacity γ r (.own 1) (rs r) ∗
      (regPointsto capacity γ r (.own 1) (rs r) -∗ initialCells capacity γ rs)) := by
  letI := capacity.registers
  unfold initialCells regPointsto
  iintro H
  iapply (BigSepM.bigSepM_lookup_acc
    (Φ := fun key value => ghost_map_elem γ (.own 1) key value)
    (initialMap_lookup rs r)).1 $$ H

/-- The full separately importable contract is proved for explicit resource capacity. -/
theorem registerSpec : RegisterSpec capacity where
  alloc := reg_alloc capacity
  cellAccess := initialCells_acc capacity
  read := reg_valid_dq capacity
  write := reg_update capacity
  writeSame := reg_interp_set_same capacity
  agree := regPointsto_agree capacity
  persist := regPointsto_persist capacity
  frameWrite := reg_update_frame capacity

end MachCSL.Logic.Registers
