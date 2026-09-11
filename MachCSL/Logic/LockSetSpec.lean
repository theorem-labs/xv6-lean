import MachCSL.Logic.LockSetDefs

namespace MachCSL.Logic.LockSet
open Iris Iris.BI

structure LockSetSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  agree : ∀ γ held name,
    iprop(⊢ auth capacity γ held -∗ member capacity γ name -∗ ⌜name ∈ held⌝)
  exclusive : ∀ γ name,
    iprop(⊢ member capacity γ name -∗ member capacity γ name -∗ False)
  insert : ∀ γ held name, name ∉ held →
    iprop(⊢ auth capacity γ held ==∗ auth capacity γ ({name} ∪ held) ∗ member capacity γ name)
  delete : ∀ γ held name,
    iprop(⊢ auth capacity γ held -∗ member capacity γ name ==∗
      ⌜name ∈ held⌝ ∗ auth capacity γ (held \ {name}))
  allocate : iprop(⊢ |==> ∃ γ, auth capacity γ ∅)
  levelIntro : ∀ γ depth held, held.size ≤ depth →
    iprop(⊢ auth capacity γ held -∗ level capacity γ depth held)
  relevel : ∀ γ depth depth' held, held.size ≤ depth' →
    iprop(⊢ level capacity γ depth held -∗ level capacity γ depth' held)
  levelZero : ∀ γ held,
    iprop(⊢ level capacity γ 0 held -∗ auth capacity γ held ∗ ⌜held = ∅⌝)
  levelInsert : ∀ γ depth held name, name ∉ held →
    iprop(⊢ level capacity γ depth held ==∗
      level capacity γ (depth + 1) ({name} ∪ held) ∗ member capacity γ name)
  levelDelete : ∀ γ depth held name,
    iprop(⊢ level capacity γ (depth + 1) held -∗ member capacity γ name ==∗
      ⌜name ∈ held⌝ ∗ level capacity γ depth (held \ {name}))

end MachCSL.Logic.LockSet
