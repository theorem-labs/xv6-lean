import Xv6.Kernel.KptHardwareSpec
import Xv6.Kernel.KptSharedLink
import Xv6.Kernel.MycpuBareGeometry

namespace Xv6.Kernel.KptHardware
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem range a (ok : KptShared.AddressOK a) : SupervisorPhysical.RamRange a 8 :=
  MycpuBare.aligned_ram_range a ((KptOwnership.aligned_iff a).mp ok.2.2) ok.1

theorem read rs a (controls : Controls rs) (ok : KptShared.AddressOK a) :
    SupervisorPteRead.Config rs a ramRegion where
  tor := controls.tor
  range := range a ok
  disabled := controls.htif
  matched := by rw [controls.pma]; exact MycpuBare.pma_ram a 8 (by decide) (range a ok)
  grant := rfl
  aligned := ok.2.2

theorem write rs a (controls : Controls rs) (ok : KptShared.AddressOK a) :
    SupervisorPteWrite.Config rs a ramRegion where
  tor := controls.tor
  range := range a ok
  disabled := controls.htif
  matched := by rw [controls.pma]; exact MycpuBare.pma_ram a 8 (by decide) (range a ok)
  grant := rfl
  aligned := ok.2.2

theorem path rs tree vpn p2 p1 (controls : Controls rs)
    (upper : KptShared.AddressOK (PtTree.addr2 tree vpn))
    (middle : KptShared.AddressOK (PtTree.addr1 p2 vpn))
    (leaf : KptShared.AddressOK (PtTree.addr0 p1 vpn)) : KptMiss.Config rs tree vpn p2 p1 regions where
  walk := by
    intro level bound
    match level with
    | 0 => exact read rs _ controls leaf
    | 1 => exact read rs _ controls middle
    | 2 => exact read rs _ controls upper
    | _ + 3 => omega
  update := ⟨read rs _ controls leaf, write rs _ controls leaf⟩

theorem pureSpec : PureSpec := ⟨range, read, write, path⟩

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem mapped rs (controls : Controls rs) era (N : Namespace) (E : CoPset) root tree vpn ppn permission
    (mask : (↑N : CoPset) ⊆ E) :
    iprop(⊢ KptShared.shared capacity era N root -∗ KptShared.snapshot capacity era tree -∗
      KptShared.mapAt capacity era vpn ppn permission ={E}=∗
      ⌜PtTree.base tree = root ∧ ∃ p2 p1 a d,
        PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission a d) ∧
        KptMiss.Config rs tree vpn p2 p1 regions⌝) := by
  iintro Hshared Hsnapshot Hmap
  imod (KptShared.nativeSpec capacity).read_path era N E root tree vpn ppn permission mask
    $$ Hshared Hsnapshot Hmap with %facts
  imodintro
  ipureintro
  obtain ⟨base,p2,p1,a,d,maps,upper,middle,leaf⟩ := facts
  exact ⟨base,p2,p1,a,d,maps,path rs tree vpn p2 p1 controls upper middle leaf⟩

theorem actual : Spec capacity := ⟨mapped capacity⟩

end Xv6.Kernel.KptHardware
