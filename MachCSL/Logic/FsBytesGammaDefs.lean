import MachCSL.Logic.FsBlocksBytesDefs
import MachCSL.Logic.FsViewLink

namespace MachCSL.Logic.FsBytesGamma
open Iris Iris.Std Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors}

/-- FsBytesGamma.fs_gamma_L, retaining the era's own byte, link and top names. -/
def logged (capacity : Disk.Capacity GF) (names : FsBlocks.Names) : FsView.View GF :=
  ⟨FsBlocks.byteElem capacity names.bytes, names.link, names.top⟩

def registryLogged (names : FsBlocks.Names) : FsView.View FsLink.registry :=
  logged FsLink.eraCapacity.disk names

end MachCSL.Logic.FsBytesGamma
