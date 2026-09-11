import MachCSL.Logic.FsViewProofs
import MachCSL.Logic.FsLinkRegistry

/-! Source `FsDurBytes.snap_gamma` at the existing native disk-image camera.
Names are parameters; fresh allocation belongs to the later snapshot allocator. -/
namespace MachCSL.Logic.FsView
open Iris Iris.Std Iris.CMRA Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors}

def snapGamma (capacity : Disk.Capacity GF) (bytes links top : GName) : View GF :=
  letI := capacity.image
  ⟨fun dq a byte => ghost_map_elem bytes dq a byte, links, top⟩

instance snapGamma_timeless (capacity : Disk.Capacity GF) bytes links top :
    GTimeless (snapGamma capacity bytes links top) where
  timeless dq a v := by
    letI := capacity.image
    change Timeless (ghost_map_elem bytes dq a v)
    infer_instance

theorem snapGamma_excl (capacity : Disk.Capacity GF) bytes links top :
    PhiExcl (snapGamma capacity bytes links top) := by
  letI := capacity.image
  intro a v w dq1 dq2
  change iprop(ghost_map_elem bytes dq1 a v ∗ ghost_map_elem bytes dq2 a w ⊢ ⌜✓ (dq1 • dq2)⌝)
  iintro H
  ihave %valid := ghost_map_elem_valid_2 bytes a dq1 dq2 v w $$ H
  ipureintro
  exact valid.1

/-- An additional native camera law; source durable consumers require only
exclusivity and timelessness, while the generic view supports fractions. -/
theorem snapGamma_frac (capacity : Disk.Capacity GF) bytes links top :
    PhiFrac (snapGamma capacity bytes links top) := by
  letI := capacity.image
  intro a v q1 q2
  exact Fractional.fractional (Φ := fun q : Qp =>
    (ghost_map_elem bytes (.own q) a v : IProp GF)) q1 q2

theorem snapGamma_full_byte (capacity : Disk.Capacity GF) bytes links top a v :
    (snapGamma capacity bytes links top).phi (.own 1) a v = Disk.imageByte capacity bytes a v := rfl

def registryGamma (bytes links top : GName) : View FsLink.registry :=
  snapGamma FsLink.eraCapacity.disk bytes links top

theorem registryGamma_excl bytes links top : PhiExcl (registryGamma bytes links top) :=
  snapGamma_excl FsLink.eraCapacity.disk bytes links top

theorem registryGamma_frac bytes links top : PhiFrac (registryGamma bytes links top) :=
  snapGamma_frac FsLink.eraCapacity.disk bytes links top

instance registryGamma_timeless bytes links top : GTimeless (registryGamma bytes links top) :=
  snapGamma_timeless FsLink.eraCapacity.disk bytes links top

/-- The camera is precisely the already registered disk-image slot. -/
theorem registryGamma_disk_slot : FsLink.eraCapacity.disk.image.elem.τ = 12 := rfl

end MachCSL.Logic.FsView
