import MachCSL.Logic.TsoHistoryDefs
import MachCSL.Machine.Node

/-! Register ownership at the actual generated dependent register types.
The source is `RiscvPtsto.v:reg_pointsto/reg_agree/reg_interp_at`. -/
namespace MachCSL.Logic.Registers
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

/-- The generated enumeration's decoder is a left inverse of its constructor index. -/
theorem ofNat_ctorIdx (r : Register) : Register.ofNat r.ctorIdx = r := by
  cases r <;> rfl

theorem ctorIdx_injective {r s : Register} (h : r.ctorIdx = s.ctorIdx) : r = s := by
  have eq := congrArg Register.ofNat h
  simpa only [ofNat_ctorIdx] using eq

/-- A lawful order on the real enumeration; no generated source is modified. -/
instance registerOrd : Ord Register := ⟨compareOn Register.ctorIdx⟩
instance registerTransOrd : _root_.Std.TransOrd Register :=
  inferInstanceAs (_root_.Std.TransCmp (compareOn Register.ctorIdx))
instance registerLawfulEqOrd : _root_.Std.LawfulEqOrd Register where
  eq_of_compare h := ctorIdx_injective (_root_.Std.LawfulEqOrd.eq_of_compare h)

abbrev Value := Sigma RegisterType
abbrev RegisterMap (V : Type) := _root_.Std.ExtTreeMap Register V
abbrev RegisterRA := HeapView Register (Agree (DiscreteO Value)) RegisterMap
abbrev RegisterRF := constOF RegisterRA

def registerFunctor : GFunctor := ⟨RegisterRF, inferInstance⟩
structure Capacity (GF : BundledGFunctors) where
  registers : GhostMapG GF Register Value RegisterMap

/-- The sole new slot follows the complete six-slot TSO algebra layer. -/
def slot : Nat := 6
def registry : BundledGFunctors := Tso.History.registry.set slot registerFunctor

theorem registry_other (i : Nat) (h : i ≠ slot) : registry i = Tso.History.registry i := by
  simp [registry, BundledGFunctors.set, h]
theorem registry_old (i : Nat) (h : i < 6) : registry i = Tso.History.registry i :=
  registry_other i (by unfold slot; omega)
theorem registry_unused (i : Nat) (h : 7 ≤ i) : registry i = Tso.History.registry i :=
  registry_other i (by unfold slot; omega)

@[reducible] def registerSlot : ElemG registry RegisterRF := ⟨6, rfl⟩
def registryCapacity : Capacity registry := ⟨⟨registerSlot⟩⟩
def historyCapacity : Tso.History.Capacity registry := ⟨⟨⟨4, rfl⟩⟩, ⟨5, rfl⟩⟩
def viewsCapacity : Tso.Views.Capacity registry := ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩
def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def regAuth (γ : GName) (dq : DFrac) (map : RegisterMap Value) : IProp GF :=
  letI := capacity.registers
  ghost_map_auth γ dq map

def regPointsto (γ : GName) (r : Register) (dq : DFrac) (value : RegisterType r) : IProp GF :=
  letI := capacity.registers
  ghost_map_elem γ dq r (⟨r, value⟩ : Value)

/-- Agreement is one-way, exactly as in the source: the owned map may be partial. -/
def RegAgree (map : RegisterMap Value) (registers : Machine.RegisterFile) : Prop :=
  ∀ r dv, PartialMap.get? map r = some dv → dv = ⟨r, registers r⟩

def regInterpAt (γ : GName) (registers : Machine.RegisterFile) : IProp GF :=
  iprop(∃ map, regAuth capacity γ (.own 1) map ∗ ⌜RegAgree map registers⌝)

/-- All constructors of the actual generated enum, with a checked completeness proof. -/
def registerCount : Nat := Register.fp_rounding_global.ctorIdx + 1

def allRegisters : List Register := (List.range registerCount).map Register.ofNat

def mapRegisters (registers : Machine.RegisterFile) : List Register → RegisterMap Value
  | [] => ∅
  | r :: rest => PartialMap.insert (mapRegisters registers rest) r ⟨r, registers r⟩

def initialMap (registers : Machine.RegisterFile) : RegisterMap Value :=
  mapRegisters registers allRegisters

/-- Initialization exports all native map fragments, without presuming read-only registers. -/
def initialCells (γ : GName) (registers : Machine.RegisterFile) : IProp GF :=
  letI := capacity.registers
  iprop([∗map] r ↦ value ∈ initialMap registers, ghost_map_elem γ (.own 1) r value)

end MachCSL.Logic.Registers
