import MachCSL.Logic.FsCrashDefs
import MachCSL.Logic.FsBytesGammaDefs
import MachCSL.Logic.FsStateLinkDefs
import MachCSL.Logic.IcacheInodeCustodyDefs
import Xv6.Fs.SnapshotConfigDefs

/-! Source FsCfgSnap's resource routing and preparation at the native
snapshot's own state. Full configuration kits remain separate resources. -/
namespace MachCSL.Logic.FsCfgSnap
open Iris Iris.Std Iris.BI Xv6.Fs
abbrev Capacity := FsCrash.BootstrapCapacity
abbrev State := DurableState.State
abbrev BlockMap := DurableState.BlockMap
abbrev Physical := Xv6.Fs.Disk

def width (state : State) : Nat := (state.superblock.ninodes / 16 + 1).toNat

/-- Facts read from the supplied snapshot and current recovery. HeaderWF is
retained from Pfs; it is not a consequence of a bare durable loan. -/
structure Prepared (physical : Physical) (covered : BlockSet) (start : Int) (state : State) : Prop where
  header : Recovery.HeaderWF (blocks physical) covered start
  recovery : FsBootRecovery.Facts physical covered start
  snapshot : Snapshot.OK state (FsBootRecovery.recovered physical covered start)
  logstart : state.superblock.logstart = start
  width_eq : (width state : Int) = state.superblock.ninodes / 16 + 1
  width_positive : 0 < width state
  width_bound : 16 * (width state : Int) ≤ 2 ^ 32
  encoded : Snapshot.OK state (SnapshotHome.restrict
    (FsBootRecovery.committed physical covered start)
    (SnapshotHome.homeSet covered state.superblock.logstart))
  exceptions_home : FsBootRecovery.exceptions physical start ⊆
    SnapshotHome.homeSet covered state.superblock.logstart
  exceptions_not_one : (1 : Int) ∉ FsBootRecovery.exceptions physical start
  metadata : ∀ b : Int, 1 ≤ b ∧ b < dataStart state.superblock → b ∈ covered

variable {GF : BundledGFunctors} (capacity : Capacity GF)

noncomputable def snapshot (g gl gt : GName) (physical : Physical)
    (covered : BlockSet) (start : Int) (state : State) : IProp GF :=
  FsDurSnapshot.fsSnap capacity.crash.disk capacity.crash.links capacity.crash.tops
    (FsView.snapGamma capacity.crash.disk g gl gt) g
    (FsBootRecovery.recovered physical covered start) state

/-- Same source guarded top-boot column as IcacheRegionSlot.topBoot, requiring
only the top capacity it actually uses. -/
def topBoot (view : FsView.View GF) (z : Int) (record : Dinode) : IProp GF :=
  if record.typeZ = 0 then
    FsTop.topFrag capacity.crash.tops view z (IcacheInodeCustody.freeNode record)
  else emp

def regionLinks (view : FsView.View GF) (state : State) (nib : Nat) : IProp GF :=
  bigSepS (fun z => IcacheInodeCustody.ireg_lnk view capacity.crash.links z
    (SnapshotConfig.node state z).record) (SnapshotConfig.regionInums nib)

def regionEntries (view : FsView.View GF) (state : State) (nib : Nat) : IProp GF :=
  bigSepS (fun z => FsState.entToksX view capacity.crash.links z
    (SnapshotConfig.node state z)) (SnapshotConfig.regionInums nib)

def liveTops (view : FsView.View GF) (state : State) (nib : Nat) : IProp GF :=
  bigSepS (fun z => FsTop.topFrag capacity.crash.tops view z
    (SnapshotConfig.node state z)) (SnapshotConfig.liveSet state nib)

def regionTopBoot (view : FsView.View GF) (state : State) (nib : Nat) : IProp GF :=
  bigSepS (fun z => topBoot capacity view z (SnapshotConfig.node state z).record)
    (SnapshotConfig.regionInums nib)

def routed (view : FsView.View GF) (state : State) (nib : Nat) : IProp GF :=
  iprop(liveTops capacity view state nib ∗ regionTopBoot capacity view state nib ∗
    regionLinks capacity view state nib ∗ regionEntries capacity view state nib)

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Complete byte-bootstrap columns plus the separately owned fresh top
map and routed inode resources. The original durable snapshot is not here. -/
def allocated (diskNames : DiskClient.Names) (physical : Physical)
    (covered : BlockSet) (start : Int) (device : BitVec 32)
    (names : FsBlocks.Names) (state : State) : IProp GF :=
  iprop(FsBootRecovery.allocated capacity.boot diskNames physical covered start
      device names.link names.top names ∗
    FsTop.auth capacity.crash.tops names.top state.inodes ∗
    routed capacity (FsBytesGamma.logged capacity.crash.disk names) state (width state))

end MachCSL.Logic.FsCfgSnap
