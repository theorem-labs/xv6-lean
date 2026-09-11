import MachCSL.Logic.StateInterpLink
import MachCSL.Logic.InvariantLink

/-! Closed resource-allocation linkage at the complete current registry.
This supplies resources and a native instance, not the initial thread WPs. -/
namespace MachCSL.Logic.MachineInterp
open Iris Iris.BI MachCSL.Machine

theorem native_initial_off_alloc (g : State) (off : g.power = false)
    (zero : g.generation = 0) (diskBytes credits : Nat) (history future : List Observation)
    (wf : ObservationsOK history g) :
    iprop(⊢ |==> ∃ (fixed : FixedNames) (native : Invariant.Names),
      ⌜fixed.diskSize = diskBytes⌝ ∗
      Invariant.allocated Invariant.registryCapacity native credits ∗
      stateInterp Invariant.machineCapacity fixed (history ++ future) g 0 future 1 ∗
      Disk.imageBytes Invariant.machineCapacity.era.disk fixed.durableDisk 0
        (Devices.Virtio.disk_read g.devices.virtio.v_disk 0 diskBytes) ∗
      PowerGhost.obsFrag Invariant.machineCapacity.power fixed.observations history) := by
  imod initial_off_alloc Invariant.machineCapacity (Disk.diskSpec _) g off zero
    diskBytes history future wf with ⟨%fixed, %size, Hstate, Hdisk, Hobs⟩
  imod Invariant.allocate Invariant.registryCapacity credits with ⟨%native, Hnative⟩
  imodintro
  iexists fixed, native
  iframe
  ipureintro
  exact size

theorem native_power_on (fixed : FixedNames) (image : BootImage) (g g' : State)
    (off : g.power = false) (shape : BootShape image g g')
    (memory : Tso.AddressMap MachCSL.Memory.Byte)
    (rep : MachCSL.Memory.FiniteMap.decode memory = g'.memory) (template : Era.Record) :
    iprop(powerInterp Invariant.machineCapacity fixed g ⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      powerInterp Invariant.machineCapacity fixed g' ∗
      generationCertificate Invariant.machineCapacity fixed g.generation era ∗
      Era.bootClients Invariant.machineCapacity.era era memory g' fixed.diskSize) :=
  power_on Invariant.machineCapacity (Era.eraSpec _ (Era.contracts _))
    fixed image g g' off shape memory rep template

end MachCSL.Logic.MachineInterp
