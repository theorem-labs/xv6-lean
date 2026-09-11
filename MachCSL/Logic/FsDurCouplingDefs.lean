import MachCSL.Logic.FsDurInodeReadDefs

/-! Source FsDurSnap §7b's byte resources for metadata coupling. This is a
name for the three source conjuncts, without added geometry or pure validity. -/
namespace MachCSL.Logic.FsDurCoupling
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState
variable {GF : BundledGFunctors}

def metadataLeg (view : FsView.View GF) (state : State) : IProp GF :=
  iprop(FsView.blockOwned view 1 state.superblockBytes ∗
    FsView.blockOwned view state.superblock.bmapstart (BitmapEncoding.bitmapBytes 1024 state.used) ∗
    FsDurInodeRead.inodeLeg view state.superblock state.inodes)

end MachCSL.Logic.FsDurCoupling
