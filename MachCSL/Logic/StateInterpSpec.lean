import MachCSL.Logic.StateInterpDefs
import MachCSL.Logic.EraSpec

namespace MachCSL.Logic.MachineInterp
open Iris Iris.BI MachCSL.Machine

/-- Initialization and generation laws only. Hardware and WP lifting are
separate contracts and are not asserted by this specification. -/
structure StateInterpSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  generationCases : ∀ names g generation era,
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗
      ⌜generation < g.generation ∨ ThreadLive g generation⌝)
  liveEraAccess : ∀ names g generation era, ThreadLive g generation →
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗
      Era.interp capacity.era era g ∗ (Era.interp capacity.era era g -∗ powerInterp capacity names g))
  powerOff : ∀ names g, g.power = true →
    iprop(powerInterp capacity names g ⊢ |==>
      (powerInterp capacity names (powerOff g) ∗
        PowerGhost.genDead capacity.power names.generation g.generation))
  powerOn : Era.EraSpec capacity.era → ∀ names image g g', g.power = false →
    BootShape image g g' → ∀ memory,
    MachCSL.Memory.FiniteMap.decode memory = g'.memory → ∀ template,
    iprop(powerInterp capacity names g ⊢ |==> ∃ era : Era.Record,
      ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ ∗ powerInterp capacity names g' ∗
      generationCertificate capacity names g.generation era ∗
      Era.bootClients capacity.era era memory g' names.diskSize)
  initialOff : Disk.DiskSpec capacity.era.disk → ∀ g,
    g.power = false → g.generation = 0 → ∀ diskBytes history future,
    ObservationsOK history g →
    iprop(⊢ |==> ∃ names : FixedNames,
      ⌜names.diskSize = diskBytes⌝ ∗ stateInterp capacity names (history ++ future) g 0 future 1 ∗
      Disk.imageBytes capacity.era.disk names.durableDisk 0
        (Devices.Virtio.disk_read g.devices.virtio.v_disk 0 diskBytes) ∗
      PowerGhost.obsFrag capacity.power names.observations history)

end MachCSL.Logic.MachineInterp
