import MachCSL.Logic.FsBootRecoverySpec
import MachCSL.Logic.FsBootBytesProofs
import Xv6.Fs.RecoveryViewProofs

namespace MachCSL.Logic.FsBootRecovery
open Iris Iris.Std Iris.BI MachCSL.Memory

theorem recovery_facts disk covered start
    (wf : Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start) : Facts disk covered start where
  full := Xv6.Fs.Recovery.recovery_disk_full _ _ _ _ rfl
  viewFull := Xv6.Fs.Recovery.view_full _ _ (Xv6.Fs.blocks_length disk)
    (Xv6.Fs.Recovery.recovery_disk_full _ _ _ _ rfl)
  domain := Xv6.Fs.Recovery.recovery_domain _ _ _ _ rfl wf
  restricted := Xv6.Fs.Recovery.recovery_restrict_view _ _ _ _ rfl wf
  raw := fun b => Xv6.Fs.Recovery.recovery_raw _ _ _ _ b rfl wf
  slot := fun i b => Xv6.Fs.Recovery.recovery_slot _ _ _ _ i b rfl wf

theorem exceptions_home disk covered start
    (wf : Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start) :
    exceptions disk start ⊆ Xv6.Fs.SnapshotHome.homeSet covered start :=
  Xv6.Fs.Recovery.writeSet_home _ _ _ wf

theorem pureSpec : PureSpec := ⟨recovery_facts, exceptions_home⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem separate_clients template era memory state length :
    Era.bootClients capacity.era era memory state length ⊣⊢
      otherClients capacity era memory state ∗
      DiskClient.diskBytes capacity.era.disk (forEra template era) 0
        (Devices.Virtio.disk_read state.devices.virtio.v_disk 0 length) := by
  unfold Era.bootClients otherClients DiskClient.diskBytes forEra
  constructor
  · iintro ⟨Hregs, Htso, Hheap, Hdevices, Hdisk, Hres⟩
    iframe
  · iintro ⟨⟨Hregs, Htso, Hheap, Hdevices, Hres⟩, Hdisk⟩
    iframe

theorem clientSpec : ClientSpec capacity := ⟨separate_clients capacity⟩

variable {hlc : HasLC} [InvGS_gen hlc GF]

theorem recovered_boot_ghosts diskNames disk length covered start device link top
    (bound : Xv6.Fs.CovIn covered length)
    (wf : Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start)
    (E : CoPset) (frame : IProp GF) :
    iprop(⊢ DiskClient.diskBytes capacity.era.disk diskNames 0 (Devices.Virtio.disk_read disk 0 length) -∗
      frame ={E}=∗ ∃ names : Names, ⌜Facts disk covered start⌝ ∗
      allocated capacity diskNames disk covered start device link top names ∗
      FsBootBytes.remainder capacity.bytes diskNames disk length covered ∗ frame) := by
  have facts := recovery_facts disk covered start wf
  iintro Hbytes Hframe
  have mint := FsBootBytes.fs_boot_ghosts capacity.bytes diskNames disk length covered
    (Xv6.Fs.SnapshotHome.homeSet covered start) device link top (committed disk covered start)
    (exceptions disk start) bound (Xv6.Fs.SnapshotHome.homeSet_subset covered start)
    (fun b _ => facts.viewFull b) (exceptions_home disk covered start wf) facts.raw E frame
  dsimp only [Capacity.bytes] at mint
  imod mint $$ Hbytes Hframe with ⟨%names, Halloc, Hrest, Hframe⟩
  imodintro
  iexists names
  unfold allocated Capacity.bytes
  iframe Halloc Hrest Hframe
  ipureintro; exact facts

theorem era_boot_ghosts template era memory state length covered start device link top
    (bound : Xv6.Fs.CovIn covered length)
    (wf : Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks state.devices.virtio.v_disk) covered start)
    (E : CoPset) (frame : IProp GF) :
    iprop(⊢ Era.interp capacity.era era state -∗
      Era.bootClients capacity.era era memory state length -∗ frame ={E}=∗
      ∃ names : Names, ⌜Facts state.devices.virtio.v_disk covered start⌝ ∗
      Era.interp capacity.era era state ∗ otherClients capacity era memory state ∗
      allocated capacity (forEra template era) state.devices.virtio.v_disk covered start device link top names ∗
      FsBootBytes.remainder capacity.bytes (forEra template era) state.devices.virtio.v_disk length covered ∗ frame) := by
  iintro Hera Hclients Hframe
  ihave ⟨Hother, Hdisk⟩ := (separate_clients capacity template era memory state length).mp $$ Hclients
  imod recovered_boot_ghosts capacity (forEra template era) state.devices.virtio.v_disk
    length covered start device link top bound wf E
    (iprop(Era.interp capacity.era era state ∗ otherClients capacity era memory state ∗ frame))
    $$ Hdisk [$Hera $Hother $Hframe] with ⟨%names, %facts, Halloc, Hrest, Hera, Hother, Hframe⟩
  imodintro
  iexists names
  iframe
  ipureintro; exact facts

theorem actual : Spec capacity := ⟨recovered_boot_ghosts capacity, era_boot_ghosts capacity⟩

end MachCSL.Logic.FsBootRecovery
