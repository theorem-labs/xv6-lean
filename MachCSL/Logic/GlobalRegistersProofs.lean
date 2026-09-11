import MachCSL.Logic.GlobalRegistersSpec

/-! Per-hart access, ownership updates, and complete eight-hart allocation. -/
namespace MachCSL.Logic.GlobalRegisters
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI MachCSL.Machine
open Iris.Std.LawfulSet
variable {GF : BundledGFunctors} (capacity : Registers.Capacity GF)

instance gregsInterp_timeless names files : Timeless (gregsInterp capacity names files) := by
  letI := capacity.registers
  unfold gregsInterp Registers.regInterpAt Registers.regAuth
  infer_instance

/-- Focus any actual hart and reassemble after replacing only that hart's file. -/
theorem gregs_acc (names : Names) (files : Files) (cpu : CPU) :
    iprop(⊢ gregsInterp capacity names files -∗
      Registers.regInterpAt capacity (names cpu) (files cpu) ∗
      (∀ rs', Registers.regInterpAt capacity (names cpu) rs' -∗
        gregsInterp capacity names (updateHart files cpu rs'))) := by
  unfold gregsInterp
  iintro H
  icases (BigSepS.bigSepS_delete (mem_allCPUs cpu)).1 $$ H with ⟨Hcur, Hrest⟩
  iframe Hcur
  iintro %rs' Hcur
  iapply (BigSepS.bigSepS_delete (mem_allCPUs cpu)).2
  have same : updateHart files cpu rs' cpu = rs' := by simp [updateHart]
  rw [same]
  iframe Hcur
  iapply BigSepS.bigSepS_mono $$ Hrest
  intro other member
  have ne : other ≠ cpu := by
    intro eq
    exact (mem_diff.mp member).2 (mem_singleton.mpr eq)
  simp only [updateHart, if_neg ne]
  exact .rfl

variable (registersSpec : Registers.RegisterSpec capacity)
include registersSpec

/-- Read at any fraction, after opening the actual hart's authoritative bridge. -/
theorem gregs_read (names : Names) (files : Files) (cpu : CPU) r dq v :
    iprop(⊢ gregsInterp capacity names files -∗
      Registers.regPointsto capacity (names cpu) r dq v -∗ ⌜files cpu r = v⌝) := by
  iintro H Hr
  ihave ⟨Hcur, _⟩ := gregs_acc capacity names files cpu $$ H
  iapply registersSpec.read (names cpu) (files cpu) r dq v $$ Hcur Hr

/-- The global update is the exact machine `updateHart` applied to its dependent write. -/
theorem gregs_write (names : Names) (files : Files) (cpu : CPU) r v v' :
    iprop(⊢ gregsInterp capacity names files -∗
      Registers.regPointsto capacity (names cpu) r (.own 1) v ==∗
      gregsInterp capacity names (updateHart files cpu (Sail.Registers.write (files cpu) r v')) ∗
      Registers.regPointsto capacity (names cpu) r (.own 1) v') := by
  iintro H Hr
  ihave ⟨Hcur, Hclose⟩ := gregs_acc capacity names files cpu $$ H
  imod registersSpec.write (names cpu) (files cpu) r v v' $$ Hcur Hr with ⟨Hcur, Hr⟩
  imodintro
  iframe Hr
  iapply Hclose $$ Hcur

private theorem alloc_set (files : Files) (cpus : CPUSet) :
    iprop(⊢ |==> ∃ names : Names,
      [∗set] cpu ∈ cpus,
        Registers.regInterpAt capacity (names cpu) (files cpu) ∗
        Registers.initialCells capacity (names cpu) (files cpu)) := by
  induction cpus using FiniteSet.set_ind with
  | hemp =>
    imodintro
    iexists (fun _ : CPU => (0 : GName))
    iapply BigSepS.bigSepS_empty.2
    itrivial
  | hadd cpu rest absent ih =>
    imod ih with ⟨%names, Hrest⟩
    imod registersSpec.alloc (files cpu) with ⟨%γ, Hcur, Hcells⟩
    imodintro
    iexists updateHart names cpu γ
    iapply (BigSepS.bigSepS_insert absent).2
    have same : updateHart names cpu γ cpu = γ := by simp [updateHart]
    rw [same]
    iframe Hcur Hcells
    iapply BigSepS.bigSepS_mono $$ Hrest
    intro other member
    have ne : other ≠ cpu := by
      intro eq
      exact absent (eq ▸ member)
    simp only [updateHart, if_neg ne]
    exact .rfl

/-- Allocate one full real register map for each of the eight harts. -/
theorem gregs_alloc (files : Files) :
    iprop(⊢ |==> ∃ names : Names,
      gregsInterp capacity names files ∗ allInitialCells capacity names files) := by
  imod alloc_set capacity registersSpec files allCPUs with ⟨%names, H⟩
  imodintro
  iexists names
  unfold gregsInterp allInitialCells
  iapply BigSepS.bigSepS_sep.1 $$ H

/-- Select one typed cell from the full eight-hart initialization bundle. -/
theorem initial_reg_acc (names : Names) (files : Files) (cpu : CPU) r :
    iprop(⊢ allInitialCells capacity names files -∗
      Registers.regPointsto capacity (names cpu) r (.own 1) (files cpu r) ∗
      (Registers.regPointsto capacity (names cpu) r (.own 1) (files cpu r) -∗
        allInitialCells capacity names files)) := by
  unfold allInitialCells
  iintro H
  ihave ⟨Hcells, Hrest⟩ := BigSepS.bigSepS_elem_of_acc (mem_allCPUs cpu) $$ H
  ihave ⟨Hr, Hcells⟩ := registersSpec.cellAccess (names cpu) (files cpu) r $$ Hcells
  iframe Hr
  iintro Hr
  iapply Hrest
  iapply Hcells $$ Hr

/-- Any additional Iris frame survives a selected hart's register write. -/
theorem gregs_write_frame (names : Names) (files : Files) (cpu : CPU) r v v' (P : IProp GF) :
    iprop(⊢ gregsInterp capacity names files ∗
      Registers.regPointsto capacity (names cpu) r (.own 1) v ∗ P ==∗
      gregsInterp capacity names (updateHart files cpu (Sail.Registers.write (files cpu) r v')) ∗
      Registers.regPointsto capacity (names cpu) r (.own 1) v' ∗ P) := by
  iintro ⟨Hi, Hr, HP⟩
  imod gregs_write capacity registersSpec names files cpu r v v' $$ Hi Hr with ⟨Hi, Hr⟩
  imodintro
  iframe Hi Hr HP

/-- Prove the global contract from an explicit per-hart contract, without its implementation. -/
theorem globalRegisterSpec : GlobalRegisterSpec capacity where
  access := gregs_acc capacity
  read := gregs_read capacity registersSpec
  write := gregs_write capacity registersSpec
  alloc := gregs_alloc capacity registersSpec
  cellAccess := initial_reg_acc capacity registersSpec
  frameWrite := gregs_write_frame capacity registersSpec

end MachCSL.Logic.GlobalRegisters
