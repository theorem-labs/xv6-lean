import MachCSL.Logic.GlobalRegistersDefs
import MachCSL.Logic.RegisterSpec

/-! Global register contract, importing the per-hart specification only. -/
namespace MachCSL.Logic.GlobalRegisters
open Iris Iris.BI MachCSL.Machine

structure GlobalRegisterSpec {GF : BundledGFunctors} (capacity : Registers.Capacity GF) : Prop where
  access : ∀ names files cpu,
    iprop(⊢ gregsInterp capacity names files -∗
      Registers.regInterpAt capacity (names cpu) (files cpu) ∗
      (∀ rs', Registers.regInterpAt capacity (names cpu) rs' -∗
        gregsInterp capacity names (updateHart files cpu rs')))
  read : ∀ names files cpu r dq v,
    iprop(⊢ gregsInterp capacity names files -∗
      Registers.regPointsto capacity (names cpu) r dq v -∗ ⌜files cpu r = v⌝)
  write : ∀ names files cpu r v v',
    iprop(⊢ gregsInterp capacity names files -∗
      Registers.regPointsto capacity (names cpu) r (.own 1) v ==∗
      gregsInterp capacity names (updateHart files cpu (Sail.Registers.write (files cpu) r v')) ∗
      Registers.regPointsto capacity (names cpu) r (.own 1) v')
  alloc : ∀ files,
    iprop(⊢ |==> ∃ names : Names,
      gregsInterp capacity names files ∗ allInitialCells capacity names files)

  cellAccess : ∀ names files cpu r,
    iprop(⊢ allInitialCells capacity names files -∗
      Registers.regPointsto capacity (names cpu) r (.own 1) (files cpu r) ∗
      (Registers.regPointsto capacity (names cpu) r (.own 1) (files cpu r) -∗
        allInitialCells capacity names files))
  frameWrite : ∀ names files cpu r v v' (P : IProp GF),
    iprop(⊢ gregsInterp capacity names files ∗
      Registers.regPointsto capacity (names cpu) r (.own 1) v ∗ P ==∗
      gregsInterp capacity names (updateHart files cpu (Sail.Registers.write (files cpu) r v')) ∗
      Registers.regPointsto capacity (names cpu) r (.own 1) v' ∗ P)

end MachCSL.Logic.GlobalRegisters
