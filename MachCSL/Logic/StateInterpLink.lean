import MachCSL.Logic.StateInterpProofs
import MachCSL.Logic.EraLink

namespace MachCSL.Logic.MachineInterp
open Iris Iris.BI MachCSL.Machine

def registryCapacity : Capacity Era.registry :=
  ⟨Era.capacity, Era.registryCapacity, { elemG := ⟨11, rfl⟩ }⟩

theorem registryStateInterpSpec : StateInterpSpec registryCapacity := stateInterpSpec registryCapacity

theorem registry_power_on (names : FixedNames) (image : BootImage) (g g' : State)
    (off : g.power = false) (shape : BootShape image g g')
    (memory : Tso.AddressMap MachCSL.Memory.Byte)
    (rep : MachCSL.Memory.FiniteMap.decode memory = g'.memory) (template : Era.Record) :
    iprop(powerInterp registryCapacity names g ⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗
      powerInterp registryCapacity names g' ∗
      generationCertificate registryCapacity names g.generation era ∗
      Era.bootClients registryCapacity.era era memory g' names.diskSize) :=
  power_on registryCapacity (Era.eraSpec _ (Era.contracts _))
    names image g g' off shape memory rep template

theorem registry_initial_off_alloc (g : State) (off : g.power = false)
    (zero : g.generation = 0) (diskBytes : Nat) (history future : List Observation)
    (wf : ObservationsOK history g) :
    iprop(⊢ |==> ∃ names : FixedNames,
      ⌜names.diskSize = diskBytes⌝ ∗ stateInterp registryCapacity names (history ++ future) g 0 future 1 ∗
      Disk.imageBytes registryCapacity.era.disk names.durableDisk 0
        (Devices.Virtio.disk_read g.devices.virtio.v_disk 0 diskBytes) ∗
      PowerGhost.obsFrag registryCapacity.power names.observations history) :=
  initial_off_alloc registryCapacity (Disk.diskSpec _) g off zero diskBytes history future wf

end MachCSL.Logic.MachineInterp
