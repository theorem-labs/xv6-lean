import MachCSL.Logic.FsDurAssembleDefs

namespace MachCSL.Logic.FsDurAssemble
open Iris Iris.Std Iris.BI Xv6.Fs DurableState

structure AssemblySpec {GF : BundledGFunctors} (view : FsView.View GF)
    (capacity : FsLink.Capacity GF) : Prop where
  slots : ∀ state disk, Snapshot.Bytes state disk →
    FsDurAlloc.slotLedger view state disk ⊢ FsState.footprint view (.own 1) state
  blocks : ∀ state disk, Snapshot.OK state disk → ∀ frame : IProp GF,
    FsDurBytes.blockLedger view disk ∗ FsState.links capacity view.link state.inodes ∗ frame ⊢
      FsState.state view capacity (.own 1) state ∗
      remainder view (FsDurBytes.flatten disk) state disk ∗ frame
  image : ∀ state disk, Snapshot.OK state disk → ∀ whole : FsDurBytes.ByteMap,
    PartialMap.submap (M := Disk.ImageMap) (FsDurBytes.flatten disk) whole → ∀ frame : IProp GF,
    FsDurBytes.byteLedger view whole ∗ FsState.links capacity view.link state.inodes ∗ frame ⊢
      FsState.state view capacity (.own 1) state ∗ remainder view whole state disk ∗ frame

end MachCSL.Logic.FsDurAssemble
