import MachCSL.Logic.DeadThreadDefs
import MachCSL.Machine.JalDevicesDefs

namespace MachCSL.Logic.ResetDiskWP
open Iris Iris.BI MachCSL.Machine

/-- Specialized to ownership of an actual reset device, without restricting the
machine's full disk transition relation. Production active-disk WPs are separate. -/
structure ResetDiskWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  resetDisk : ∀ image fixed whole generation era previous post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      Device.virtioFrag capacity.era.devices era.virtio (Devices.Virtio.virtio_reset previous) -∗
      DeadThread.threadWP capacity image fixed whole (.disk generation) post)

end MachCSL.Logic.ResetDiskWP
