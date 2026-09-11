import MachCSL.Logic.FsCfgSnapReadProofs
import MachCSL.Logic.FsCfgSnapRouteProofs
import MachCSL.Logic.FsStateLinkAllocProofs

namespace MachCSL.Logic.FsCfgSnap
open Iris Iris.Std Iris.BI Xv6.Fs
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem allocated_names diskNames physical covered start device link top names :
    FsBootRecovery.allocated capacity.boot diskNames physical covered start device link top names ⊢
      ⌜names.link = link ∧ names.top = top⌝ := by
  unfold FsBootRecovery.allocated FsBootBytes.allocated
  iintro ⟨%hl, %ht, _⟩
  ipureintro; exact ⟨hl, ht⟩

/-- FsCfgSnap section9's runtime link/top mint is justified by the held
snapshot's readback. The original named snapshot is retained. -/
theorem allocate diskNames physical length covered start device g gl gt state
    (startTwo : start = 2) (logCovered : SnapshotHome.logRegion start ⊆ covered)
    (coveredIn : CovIn covered length) (header : Recovery.HeaderWF (blocks physical) covered start)
    (E : CoPset) (frame : IProp GF) :
    iprop(⊢ snapshot capacity g gl gt physical covered start state -∗
      DiskClient.diskBytes capacity.boot.era.disk diskNames 0 (Devices.Virtio.disk_read physical 0 length) -∗
      frame ={E}=∗ ∃ names : FsBlocks.Names, ⌜Prepared physical covered start state⌝ ∗
        snapshot capacity g gl gt physical covered start state ∗
        allocated capacity diskNames physical covered start device names state ∗
        FsBootBytes.remainder capacity.boot.bytes diskNames physical length covered ∗ frame) := by
  iintro Hsnap Hdisk Hframe
  ihave ⟨%facts, Hsnap⟩ := prepare capacity g gl gt physical covered start state startTwo logCovered header $$ Hsnap
  obtain ⟨choices, ty, choicesOK, valid⟩ := facts.snapshot.1.links
  imod FsState.boot_alloc_root_slack capacity.crash.links capacity.crash.tops
    state.inodes choices 1 ty choicesOK valid with ⟨%link, %top, Htop, Hfrags, Hlinks, Hkeep⟩
  imod FsBootRecovery.recovered_boot_ghosts capacity.boot diskNames physical length covered start device link top
    coveredIn header E frame $$ Hdisk Hframe with ⟨%names, %_recovery, Halloc, Hrest, Hframe⟩
  ihave %ties := allocated_names capacity diskNames physical covered start device link top names $$ Halloc
  rcases ties with ⟨rfl, rfl⟩
  have linkRoute : iprop(⊢ FsState.links capacity.crash.links names.link state.inodes -∗
      FsLink.tok capacity.crash.links names.link 1 ty -∗
      regionLinks capacity (FsBytesGamma.logged capacity.crash.disk names) state (width state) ∗
      regionEntries capacity (FsBytesGamma.logged capacity.crash.disk names) state (width state)) :=
    link_route capacity (FsBytesGamma.logged capacity.crash.disk names)
      state _ (width state) ty facts.snapshot.1 facts.width_eq facts.width_positive
  ihave ⟨Hlnks, Hentries⟩ := linkRoute $$ Hlinks Hkeep
  have topRoute : FsTop.allFragments capacity.crash.tops names.top state.inodes ⊢
      liveTops capacity (FsBytesGamma.logged capacity.crash.disk names) state (width state) ∗
      regionTopBoot capacity (FsBytesGamma.logged capacity.crash.disk names) state (width state) :=
    top_route capacity (FsBytesGamma.logged capacity.crash.disk names)
      state _ (width state) facts.snapshot facts.width_eq
  ihave ⟨Hlive, Hboot⟩ := topRoute $$ Hfrags
  imodintro
  iexists names
  isplit
  · ipureintro; exact facts
  isplitl [Hsnap]
  · iexact Hsnap
  isplitl [Halloc Htop Hlive Hboot Hlnks Hentries]
  · unfold allocated routed
    iframe Halloc Htop Hlive Hboot Hlnks Hentries
  · iframe Hrest Hframe

theorem era_allocate crashNames template era memory machine length covered start device
    (startTwo : start = 2) (logCovered : SnapshotHome.logRegion start ⊆ covered)
    (coveredIn : CovIn covered length) (E : CoPset) (frame : IProp GF) :
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
          machine.devices.virtio.v_disk length covered ∗ frame) := by
  iintro Hp Hera Hclients Hframe
  imod loan capacity crashNames covered start machine.devices.virtio.v_disk frame $$ Hp Hframe
    with ⟨%header, Hp, Hloan, Hframe⟩
  ihave ⟨%g, %gl, %gt, %state, %_ok, Hsnap⟩ :=
    open_loan capacity covered start machine.devices.virtio.v_disk $$ Hloan
  ihave ⟨Hother, Hdisk⟩ :=
    (FsBootRecovery.separate_clients capacity.boot template era memory machine length).mp $$ Hclients
  imod allocate capacity (FsBootRecovery.forEra template era) machine.devices.virtio.v_disk
    length covered start device g gl gt state startTwo logCovered coveredIn header E frame
    $$ Hsnap Hdisk Hframe with ⟨%names, %facts, Hsnap, Halloc, Hrest, Hframe⟩
  imodintro
  iexists g, gl, gt, state, names
  isplit
  · ipureintro; exact facts
  · iframe Hp Hsnap Hera Hother Halloc Hrest Hframe

theorem actual : Spec capacity := ⟨allocate capacity, era_allocate capacity⟩

end MachCSL.Logic.FsCfgSnap
