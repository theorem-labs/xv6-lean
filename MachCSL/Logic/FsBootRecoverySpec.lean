import MachCSL.Logic.FsBootRecoveryDefs

namespace MachCSL.Logic.FsBootRecovery
open Iris Iris.Std Iris.BI MachCSL.Memory

structure PureSpec : Prop where
  facts : ∀ disk covered start, Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start →
    Facts disk covered start
  exceptions_home : ∀ disk covered start, Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start →
    exceptions disk start ⊆ Xv6.Fs.SnapshotHome.homeSet covered start

structure ClientSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  separate : ∀ template era memory state length,
    Era.bootClients capacity.era era memory state length ⊣⊢
      otherClients capacity era memory state ∗
      DiskClient.diskBytes capacity.era.disk (forEra template era) 0
        (Devices.Virtio.disk_read state.devices.virtio.v_disk 0 length)

structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  recovered_boot_ghosts : ∀ diskNames disk length covered start device link top,
    Xv6.Fs.CovIn covered length → Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start →
    ∀ (E : CoPset) (frame : IProp GF),
    iprop(⊢ DiskClient.diskBytes capacity.era.disk diskNames 0 (Devices.Virtio.disk_read disk 0 length) -∗
      frame ={E}=∗ ∃ names : Names, ⌜Facts disk covered start⌝ ∗
      allocated capacity diskNames disk covered start device link top names ∗
      FsBootBytes.remainder capacity.bytes diskNames disk length covered ∗ frame)
  era_boot_ghosts : ∀ template era memory state length covered start device link top,
    Xv6.Fs.CovIn covered length →
    Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks state.devices.virtio.v_disk) covered start →
    ∀ (E : CoPset) (frame : IProp GF),
    iprop(⊢ Era.interp capacity.era era state -∗
      Era.bootClients capacity.era era memory state length -∗ frame ={E}=∗
      ∃ names : Names, ⌜Facts state.devices.virtio.v_disk covered start⌝ ∗
      Era.interp capacity.era era state ∗ otherClients capacity era memory state ∗
      allocated capacity (forEra template era) state.devices.virtio.v_disk covered start device link top names ∗
      FsBootBytes.remainder capacity.bytes (forEra template era) state.devices.virtio.v_disk length covered ∗ frame)

end MachCSL.Logic.FsBootRecovery
