import MachCSL.Logic.RegisterDefs

/-! The public register bridge contract, independent of its proof implementation. -/
namespace MachCSL.Logic.Registers
open Iris Iris.BI

structure RegisterSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  alloc : ∀ rs,
    iprop(⊢ |==> ∃ γ, regInterpAt capacity γ rs ∗ initialCells capacity γ rs)
  cellAccess : ∀ γ rs r,
    iprop(⊢ initialCells capacity γ rs -∗
      regPointsto capacity γ r (.own 1) (rs r) ∗
      (regPointsto capacity γ r (.own 1) (rs r) -∗ initialCells capacity γ rs))
  read : ∀ γ rs r dq v,
    iprop(⊢ regInterpAt capacity γ rs -∗ regPointsto capacity γ r dq v -∗ ⌜rs r = v⌝)
  write : ∀ γ rs r v v',
    iprop(⊢ regInterpAt capacity γ rs -∗ regPointsto capacity γ r (.own 1) v ==∗
      regInterpAt capacity γ (Sail.Registers.write rs r v') ∗
      regPointsto capacity γ r (.own 1) v')
  writeSame : ∀ γ rs r v, rs r = v →
    iprop(⊢ regInterpAt capacity γ rs -∗ regInterpAt capacity γ (Sail.Registers.write rs r v))
  agree : ∀ γ r dq1 dq2 v1 v2,
    iprop(regPointsto capacity γ r dq1 v1 ∗ regPointsto capacity γ r dq2 v2 ⊢ ⌜v1 = v2⌝)
  persist : ∀ γ r dq v,
    iprop(⊢ regPointsto capacity γ r dq v ==∗ regPointsto capacity γ r .discard v)
  frameWrite : ∀ γ rs r v v' (P : IProp GF),
    iprop(⊢ regInterpAt capacity γ rs ∗ regPointsto capacity γ r (.own 1) v ∗ P ==∗
      regInterpAt capacity γ (Sail.Registers.write rs r v') ∗
      regPointsto capacity γ r (.own 1) v' ∗ P)

end MachCSL.Logic.Registers
