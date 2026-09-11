import MachCSL.Logic.IcacheTopRegistryDefs

/-! Exact native retag contracts from InodeRegion.v:3294–3340. -/
namespace MachCSL.Logic.IcacheTopRetag
open Iris Iris.BI IcacheTopRegistry

structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  retag : ∀ names (N : Namespace) (E : CoPset) i old new,
    (↑N : CoPset) ⊆ E → Xv6.Fs.DurableNode.Local i new →
    iprop(⊢ invariant capacity names N -∗ FsTop.frag capacity.top names.top i old
      ={E}=∗ FsTop.frag capacity.top names.top i new)
  retag_armed : ∀ names (N : Namespace) (E : CoPset) k t q (S : InumSet) i old new,
    (↑N : CoPset) ⊆ E → i ∈ S →
    iprop(⊢ invariant capacity names N -∗ armed capacity names k t q S -∗
      FsTop.frag capacity.top names.top i old ={E}=∗
      armed capacity names k t q S ∗ FsTop.frag capacity.top names.top i new)

end MachCSL.Logic.IcacheTopRetag
