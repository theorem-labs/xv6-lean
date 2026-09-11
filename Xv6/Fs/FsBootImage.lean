import Xv6.Fs.BootImageImage
import MachCSL.Logic.FsBootRecoveryLink

/-! Literal clean-image specialization of actual era disk bootstrap. The
state-to-artifact disk equality is explicit; physical ownership stays at the
original era name and is never reminted from an initial snapshot. -/
set_option maxRecDepth 2048

namespace Xv6.Fs.Image
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Logic

theorem boot_header_zero : Recovery.headerN (blockView superblock.logstart) = 0 := by
  change (assembleBytes ((blockView superblock.logstart).take 4) : Int) = 0
  rw [(logClean_iff blockView superblock).mp log_clean]
  rfl

theorem boot_header_wf : Recovery.HeaderWF blockView initialCoverage superblock.logstart :=
  Recovery.headerWF_zero _ _ _ boot_header_zero

theorem boot_recovered_home :
    FsBootRecovery.recovered disk initialCoverage superblock.logstart =
      SnapshotHome.homeMap blockView initialCoverage superblock.logstart :=
  Recovery.recovery_clean _ _ _ _ boot_header_zero rfl

theorem boot_exceptions_empty : FsBootRecovery.exceptions disk superblock.logstart = ∅ := by
  unfold FsBootRecovery.exceptions Recovery.writeSet
  change Std.ExtTreeSet.ofList (Recovery.headerDecode (blockView superblock.logstart)).2 = _
  rw [Recovery.headerDecode_zero _ boot_header_zero]
  rfl

theorem boot_committed_raw b :
    FsBootRecovery.committed disk initialCoverage superblock.logstart b = blockView b := by
  unfold FsBootRecovery.committed
  rw [boot_recovered_home]
  unfold Recovery.view SnapshotHome.homeMap
  rw [SnapshotHome.restrict_lookup]
  split <;> rfl

theorem boot_recovery_facts : FsBootRecovery.Facts disk initialCoverage superblock.logstart :=
  FsBootRecovery.recovery_facts _ _ _ boot_header_wf

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]

theorem boot_era_filesystem (capacity : FsBootRecovery.Capacity GF)
    (template : DiskClient.Names) (era : Era.Record) (memory : Tso.AddressMap Byte)
    (state : MachCSL.Machine.State) (device : BitVec 32) (link top : GName)
    (sameDisk : state.devices.virtio.v_disk = disk) (E : CoPset) (frame : IProp GF) :
    iprop(⊢ Era.interp capacity.era era state -∗
      Era.bootClients capacity.era era memory state 2048000 -∗ frame ={E}=∗
      ∃ names : FsBootRecovery.Names, ⌜FsBootRecovery.Facts disk initialCoverage superblock.logstart⌝ ∗
      Era.interp capacity.era era state ∗ FsBootRecovery.otherClients capacity era memory state ∗
      FsBootRecovery.allocated capacity (FsBootRecovery.forEra template era) disk initialCoverage
        superblock.logstart device link top names ∗
      FsBootBytes.remainder capacity.bytes (FsBootRecovery.forEra template era) disk 2048000 initialCoverage ∗ frame) := by
  have wf : Recovery.HeaderWF (blocks state.devices.virtio.v_disk) initialCoverage superblock.logstart := by
    rw [sameDisk]
    exact boot_header_wf
  have mint := FsBootRecovery.era_boot_ghosts capacity template era memory state 2048000
    initialCoverage superblock.logstart device link top boot_image_wf.coverage wf E frame
  rw [sameDisk] at mint
  exact mint

end Xv6.Fs.Image
