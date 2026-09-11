import MachCSL.Logic.EraRegistry

namespace MachCSL.Logic.Era
open Iris Iris.Std Iris.BI
variable {GF : BundledGFunctors} (registryCap : RegistryCapacity GF)

instance registered_persistent name generation era :
    Persistent (registered registryCap name generation era) := by
  letI := registryCap.entries
  unfold registered
  infer_instance

instance registered_timeless name generation era :
    Timeless (registered registryCap name generation era) := by
  letI := registryCap.entries
  unfold registered
  infer_instance

theorem registry_alloc :
    iprop(⊢ |==> ∃ name, registryAuth registryCap name ∅) := by
  letI := registryCap.entries
  exact ghost_map_alloc_empty

theorem registry_lookup name entries generation era :
    iprop(⊢ registryAuth registryCap name entries -∗ registered registryCap name generation era -∗
      ⌜entries[generation]? = some era⌝) := by
  letI := registryCap.entries
  exact ghost_map_lookup

theorem registered_agree name generation era era' :
    iprop(registered registryCap name generation era ∗ registered registryCap name generation era' ⊢
      ⌜era = era'⌝) := by
  letI := registryCap.entries
  exact ghost_map_elem_agree name generation .discard .discard era era'

theorem registry_insert name entries generation era (fresh : entries[generation]? = none) :
    iprop(registryAuth registryCap name entries ⊢ |==>
      (registryAuth registryCap name (PartialMap.insert entries generation era) ∗
      registered registryCap name generation era)) := by
  letI := registryCap.entries
  unfold registryAuth registered
  iintro H
  iapply ghost_map_insert_persist (GF := GF) (γ := name) (m := entries) generation era fresh $$ H

end MachCSL.Logic.Era
