import Xv6.Kernel.KptSharedSpec
import Xv6.Kernel.KptSharedPureProofs
import Xv6.Kernel.KptOwnershipSpec
import MachCSL.Logic.KptGhostProofs

namespace Xv6.Kernel.KptShared
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)
    (ownership : KptOwnership.Spec capacity)

include ownership in
theorem body_timeless era root : Timeless (body capacity era root) := by
  haveI (B : Nat) (tree : PtTree.Tree) :
      Timeless (KptOwnership.treeOwn capacity era (.kernel B) 2 (.own 1) tree) :=
    ownership.tree_timeless era (.kernel B) 2 (.own 1) tree
  unfold body
  infer_instance

instance snapshot_persistent era tree : Persistent (snapshot capacity era tree) := by
  unfold snapshot
  infer_instance
instance bound_persistent era B : Persistent (bound capacity era B) := by
  unfold bound
  infer_instance
instance mapAt_persistent era vpn ppn permission : Persistent (mapAt capacity era vpn ppn permission) := by
  unfold mapAt
  infer_instance

include ownership in
theorem slot_address era tier a dq w :
    iprop(KptOwnership.slotOwn capacity era tier a dq w ⊢ ⌜AddressOK a⌝) := by
  iintro Hslot
  ihave %ram := ownership.slot_ram era tier a dq w $$ Hslot
  ihave %ram7 := ownership.slot_ram7 era tier a dq w $$ Hslot
  ihave %aligned := ownership.slot_aligned era tier a dq w $$ Hslot
  ipureintro
  exact ⟨ram,ram7,aligned⟩

variable {hlc : HasLC} [InvGS_gen hlc GF]
instance shared_persistent era N root : Persistent (shared capacity era N root) := by
  unfold shared
  infer_instance

/-- Allocate exactly the source body from its already-owned physical table. -/
theorem allocate era (N : Namespace) (E : CoPset) root mapping tree B
    (spec : TreeSpec root mapping tree) :
    iprop(⊢ KptOwnership.treeOwn capacity era (.kernel B) 2 (.own 1) tree -∗
      KptGhost.mapAuth capacity.ghost era.kernelMap mapping -∗
      Tso.Views.llb capacity.machine.era.views era.logLength B -∗
      KptGhost.unset capacity.ghost era.kernelPageTable -∗
      KptGhost.boundUnset capacity.ghost era.kernelPageTableBound ={E}=∗
      shared capacity era N root ∗ snapshot capacity era tree ∗ bound capacity era B) := by
  iintro Htree Hmap Hllb Hpending HboundPending
  imod KptGhost.shoot capacity.ghost era.kernelPageTable tree $$ Hpending with #Hsnapshot
  imod KptGhost.shoot_bound capacity.ghost era.kernelPageTableBound era.logLength B
    $$ [Hllb HboundPending] with #Hbound
  · iframe Hllb HboundPending
  imod inv_alloc N E (body capacity era root) $$ [Htree Hmap] with #Hshared
  · iintro !>
    iunfold body
    iexists tree, mapping, B
    iframe Htree Hmap Hsnapshot Hbound
    ipureintro
    exact spec
  imodintro
  unfold shared snapshot bound
  iframe Hshared Hsnapshot Hbound

include ownership in
theorem read_snapshot era (N : Namespace) (E : CoPset) root (mask : (↑N : CoPset) ⊆ E) :
    iprop(⊢ shared capacity era N root ={E}=∗ ∃ tree, snapshot capacity era tree) := by
  haveI := body_timeless capacity ownership era root
  iintro #Hshared
  iunfold shared at Hshared
  imod inv_acc mask $$ Hshared with ⟨Hbody,Hclose⟩
  imod Hbody
  iunfold body at Hbody
  icases Hbody with ⟨%tree,%mapping,%B,Htree,#Hsnapshot,#Hbound,Hmap,%spec⟩
  imod Hclose $$ [Htree Hmap] with _
  · iintro !>
    iunfold body
    iexists tree, mapping, B
    iframe Htree Hmap Hsnapshot Hbound
    ipureintro
    exact spec
  imodintro
  iexists tree
  iexact Hsnapshot

include ownership in
theorem read_path era (N : Namespace) (E : CoPset) root tree vpn ppn permission
    (mask : (↑N : CoPset) ⊆ E) :
    iprop(⊢ shared capacity era N root -∗ snapshot capacity era tree -∗
      mapAt capacity era vpn ppn permission ={E}=∗
      ⌜PtTree.base tree = root ∧ ∃ p2 p1 a d,
        PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission a d) ∧
        AddressOK (PtTree.addr2 tree vpn) ∧ AddressOK (PtTree.addr1 p2 vpn) ∧
        AddressOK (PtTree.addr0 p1 vpn)⌝) := by
  haveI := body_timeless capacity ownership era root
  iintro #Hshared #Hgiven #Hclaim
  iunfold shared at Hshared
  imod inv_acc mask $$ Hshared with ⟨Hbody,Hclose⟩
  imod Hbody
  iunfold body at Hbody
  icases Hbody with ⟨%current,%mapping,%B,Htree,#Hsnapshot,#Hbound,Hmap,%spec⟩
  ihave %found := KptGhost.map_lookup capacity.ghost era.kernelMap mapping vpn ppn permission
    $$ [Hmap Hclaim]
  · iframe Hmap Hclaim
  ihave %same := KptGhost.agree capacity.ghost era.kernelPageTable current tree $$ [Hsnapshot Hgiven]
  · iframe Hsnapshot Hgiven
  obtain ⟨p2,p1,a,d,mapped⟩ := map_path root mapping current spec vpn ppn permission found
  ihave ⟨Hslot2,Hslot1,Hslot0,Hrestore⟩ := ownership.path_ro era (.kernel B) (.own 1) current vpn p2 p1 _ mapped $$ Htree
  ihave %address2 := slot_address capacity ownership era (.kernel B) _ (.own 1) p2 $$ Hslot2
  ihave %address1 := slot_address capacity ownership era (.kernel B) _ (.own 1) p1 $$ Hslot1
  ihave %address0 := slot_address capacity ownership era (.kernel B) _ (.own 1) _ $$ Hslot0
  ihave Htree := Hrestore $$ Hslot2 Hslot1 Hslot0
  imod Hclose $$ [Htree Hmap] with _
  · iintro !>
    iunfold body
    iexists current, mapping, B
    iframe Htree Hmap Hsnapshot Hbound
    ipureintro
    exact spec
  imodintro
  ipureintro
  have bases := congrArg PtTree.base same
  change PtTree.base current = PtTree.base tree at bases
  refine ⟨bases.symm.trans spec.1, ?_⟩
  obtain ⟨word,wordMaps,canonical⟩ := PtTree.maps_across current tree vpn p2 p1 _ same mapped
  obtain ⟨a',d',wordEq⟩ := Sv39Walk.leaf_variant ppn permission word (by
    rw [canonical, KptLeaf.word_canonical, KptLeaf.word_canonical])
  refine ⟨p2,p1,a',d',wordEq ▸ wordMaps,?_,address1,address0⟩
  simpa only [PtTree.addr2, bases] using address2

include ownership in
theorem actual : Spec capacity :=
  ⟨body_timeless capacity ownership, allocate capacity,
    read_snapshot capacity ownership, read_path capacity ownership⟩

end Xv6.Kernel.KptShared
