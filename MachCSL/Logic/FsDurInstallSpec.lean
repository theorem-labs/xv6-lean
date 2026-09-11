import MachCSL.Logic.FsDurInstallDefs

namespace MachCSL.Logic.FsDurInstall
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurXferRuns
variable {GF : BundledGFunctors}

structure InstallSpec (view : FsView.View GF) (lc : FsLink.Capacity GF) : Prop where
  mapSplit : ∀ part whole, PartialMap.submap (M := Disk.ImageMap) part whole →
    phiMap view whole ⊣⊢ phiMap view part ∗ phiMap view (PartialMap.difference (M := Disk.ImageMap) whole part)
  footprint : ∀ state pool whole, Facts state pool whole → phiMap view whole ⊢
    FsState.footprint view (.own 1) state ∗ phiMap view (remainder state pool whole)
  state : ∀ state pool whole, Facts state pool whole → phiMap view whole ∗ FsState.ghost view lc state ⊢
    FsState.state view lc (.own 1) state ∗ phiMap view (remainder state pool whole)

structure SourceSpec (dc : Disk.Capacity GF) : Prop where
  facts : ∀ g gl gt whole state, Disk.mapAuth dc g whole ∗ FsState.footprint (FsView.snapGamma dc g gl gt) (.own 1) state ⊢
    ∃ pool, ⌜Facts state pool whole⌝

end MachCSL.Logic.FsDurInstall
