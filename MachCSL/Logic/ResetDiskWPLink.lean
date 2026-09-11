import MachCSL.Logic.ResetDiskWPProofs
import MachCSL.Logic.InvariantLink

namespace MachCSL.Logic.ResetDiskWP
open Iris Iris.BI MachCSL.Machine

theorem registryResetDiskWPSpec [Platform] (names : Invariant.Names) :
    letI := names.native Invariant.registryCapacity
    ResetDiskWPSpec Invariant.machineCapacity := by
  letI := names.native Invariant.registryCapacity
  exact resetDiskWPSpec Invariant.machineCapacity

theorem registry_wp_reset_disk [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (previous : Devices.Virtio.State)
    (post : Empty → IProp Invariant.registry) :
    letI := names.native Invariant.registryCapacity
    iprop(⊢ MachineInterp.generationCertificate Invariant.machineCapacity fixed generation era -∗
      Device.virtioFrag Invariant.machineCapacity.era.devices era.virtio (Devices.Virtio.virtio_reset previous) -∗
      DeadThread.threadWP Invariant.machineCapacity image fixed whole (.disk generation) post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_reset_disk Invariant.machineCapacity image fixed whole generation era previous post

end MachCSL.Logic.ResetDiskWP
