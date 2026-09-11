import MachCSL.Logic.FsCfgSnapDefs

namespace MachCSL.Logic.FsCfgSnap
open Iris Iris.Std Iris.BI Xv6.Fs
variable {GF : BundledGFunctors}

structure RouteSpec (capacity : Capacity GF) : Prop where
  map_as_set : ∀ (nodes : DurableState.InodeMap) (phi : Int → DurableNode.Node → IProp GF),
    bigSepM (M := FsState.InodeMap) phi nodes ⊣⊢
      bigSepS (fun i => phi i (nodes[i]?.getD SnapshotConfig.defaultNode))
        (FiniteMap.dom_set (M := FsState.InodeMap) (S := BlockSet) nodes)
  links_to_region : ∀ gl state disk (nib : Nat),
    Snapshot.Bytes state disk → (nib : Int) = state.superblock.ninodes / 16 + 1 →
    FsState.links capacity.crash.links gl state.inodes ⊢
      bigSepS (fun z => FsState.linkNode capacity.crash.links gl z
        (SnapshotConfig.node state z)) (SnapshotConfig.regionInums nib)
  link_route : ∀ (view : FsView.View GF) state disk (nib : Nat) ty,
    Snapshot.Bytes state disk → (nib : Int) = state.superblock.ninodes / 16 + 1 → 0 < nib →
    iprop(⊢ FsState.links capacity.crash.links view.link state.inodes -∗
      FsLink.tok capacity.crash.links view.link 1 ty -∗
      regionLinks capacity view state nib ∗ regionEntries capacity view state nib)
  top_route : ∀ (view : FsView.View GF) state disk (nib : Nat),
    Snapshot.OK state disk → (nib : Int) = state.superblock.ninodes / 16 + 1 →
    FsTop.allFragments capacity.crash.tops view.top state.inodes ⊢
      liveTops capacity view state nib ∗ regionTopBoot capacity view state nib

structure ReadSpec (capacity : Capacity GF) : Prop where
  loan : ∀ names covered start physical (frame : IProp GF),
    iprop(⊢ FsCrash.Pfs capacity.crash names covered start physical -∗ frame ==∗
      ⌜Recovery.HeaderWF (blocks physical) covered start⌝ ∗
      FsCrash.Pfs capacity.crash names covered start physical ∗
      FsCrash.lend capacity.crash covered start physical ∗ frame)
  open_loan : ∀ covered start physical,
    FsCrash.lend capacity.crash covered start physical ⊢
      ∃ g gl gt state, ⌜Snapshot.OK state (FsBootRecovery.recovered physical covered start)⌝ ∗
        snapshot capacity g gl gt physical covered start state
  prepare : ∀ g gl gt physical covered start state,
    start = 2 → SnapshotHome.logRegion start ⊆ covered →
    Recovery.HeaderWF (blocks physical) covered start →
    snapshot capacity g gl gt physical covered start state ⊢
      ⌜Prepared physical covered start state⌝ ∗ snapshot capacity g gl gt physical covered start state

structure Spec {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF) : Prop where
  allocate : ∀ diskNames physical length covered start device g gl gt state,
    start = 2 → SnapshotHome.logRegion start ⊆ covered → CovIn covered length →
    Recovery.HeaderWF (blocks physical) covered start → ∀ (E : CoPset) (frame : IProp GF),
    iprop(⊢ snapshot capacity g gl gt physical covered start state -∗
      DiskClient.diskBytes capacity.boot.era.disk diskNames 0
        (Devices.Virtio.disk_read physical 0 length) -∗ frame ={E}=∗
      ∃ names : FsBlocks.Names, ⌜Prepared physical covered start state⌝ ∗
        snapshot capacity g gl gt physical covered start state ∗
        allocated capacity diskNames physical covered start device names state ∗
        FsBootBytes.remainder capacity.boot.bytes diskNames physical length covered ∗ frame)
  era_allocate : ∀ crashNames template era memory machine length covered start device,
    start = 2 → SnapshotHome.logRegion start ⊆ covered → CovIn covered length →
    ∀ (E : CoPset) (frame : IProp GF),
    iprop(⊢ FsCrash.Pfs capacity.crash crashNames covered start machine.devices.virtio.v_disk -∗
      Era.interp capacity.boot.era era machine -∗
      Era.bootClients capacity.boot.era era memory machine length -∗ frame ={E}=∗
      ∃ (g gl gt : GName) (state : State) (names : FsBlocks.Names),
        ⌜Prepared machine.devices.virtio.v_disk covered start state⌝ ∗
        FsCrash.Pfs capacity.crash crashNames covered start machine.devices.virtio.v_disk ∗
        snapshot capacity g gl gt machine.devices.virtio.v_disk covered start state ∗
        Era.interp capacity.boot.era era machine ∗
        FsBootRecovery.otherClients capacity.boot era memory machine ∗
        allocated capacity (FsBootRecovery.forEra template era) machine.devices.virtio.v_disk
          covered start device names state ∗
        FsBootBytes.remainder capacity.boot.bytes (FsBootRecovery.forEra template era)
          machine.devices.virtio.v_disk length covered ∗ frame)

end MachCSL.Logic.FsCfgSnap
