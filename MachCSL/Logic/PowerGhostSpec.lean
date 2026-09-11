import MachCSL.Logic.PowerGhostDefs

/-! Fixed-component contract, independent of the implementation and final era registry. -/
namespace MachCSL.Logic.PowerGhost
open Iris Iris.BI MachCSL.Machine

structure PowerGhostSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  genAlloc : ∀ n, iprop(⊢ |==> ∃ γ, genAuth capacity γ n ∗ genBorn capacity γ n)
  genUpdate : ∀ γ n n', n ≤ n' →
    iprop(⊢ genAuth capacity γ n ==∗ genAuth capacity γ n' ∗ genBorn capacity γ n')
  genDie : ∀ γ generation,
    iprop(⊢ genAuth capacity γ generation ==∗
      genAuth capacity γ (generation + 1) ∗ genDead capacity γ generation)
  startMark : ∀ γ generation,
    iprop(⊢ startAuth capacity γ generation ==∗
      startAuth capacity γ (generation + 1) ∗ genStarted capacity γ generation)
  genValid : ∀ γ n generation,
    iprop(⊢ genAuth capacity γ n -∗ genBorn capacity γ generation -∗ ⌜generation ≤ n⌝)
  deadValid : ∀ γ n generation,
    iprop(⊢ genAuth capacity γ n -∗ genDead capacity γ generation -∗ ⌜generation < n⌝)
  startedValid : ∀ γ n generation,
    iprop(⊢ startAuth capacity γ n -∗ genStarted capacity γ generation -∗ ⌜generation < n⌝)
  obsAlloc : ∀ history,
    iprop(⊢ |==> ∃ γ, obsAuth capacity γ history ∗ obsFrag capacity γ history)
  obsAgree : ∀ γ h1 h2,
    iprop(⊢ obsAuth capacity γ h1 -∗ obsFrag capacity γ h2 -∗ ⌜h1 = h2⌝)
  obsUpdate : ∀ γ history history',
    iprop(⊢ obsAuth capacity γ history -∗ obsFrag capacity γ history ==∗
      obsAuth capacity γ history' ∗ obsFrag capacity γ history')
  obsSilent : ∀ [Platform] image e e' g g' forks, Step image e g [] e' g' forks →
    ∀ γ whole future,
      iprop(obsInterp capacity γ whole g future ⊢ obsInterp capacity γ whole g' future)
  obsClose : ∀ [Platform] image e e' g g' events forks history future whole,
    Step image e g events e' g' forks → ObservationsOK history g →
    history ++ (events ++ future) = whole → ∀ γ,
      iprop(obsAuth capacity γ (history ++ events) ⊢ obsInterp capacity γ whole g' future)
  obsFinished : ∀ γ whole g,
    iprop(obsInterp capacity γ whole g [] ⊢ obsAuth capacity γ whole ∗ ⌜ObservationsOK whole g⌝)
  counterStep : ∀ [Platform] image e e' g g' events forks,
    Step image e g events e' g' forks → ∀ names,
      iprop(counterInterp capacity names g ⊢ |==> counterInterp capacity names g')
  fixedAlloc : ∀ g history future, ObservationsOK history g →
    iprop(⊢ |==> ∃ names : Names, counterInterp capacity names g ∗
      obsInterp capacity names.observations (history ++ future) g future ∗
      obsFrag capacity names.observations history)

end MachCSL.Logic.PowerGhost
