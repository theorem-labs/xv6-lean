import Xv6.Kernel.KptSharedPureDefs
import Xv6.Kernel.PtTreeLink
import Xv6.Kernel.Sv39WalkPure

namespace Xv6.Kernel.KptShared
open MachCSL.Machine MachCSL.Logic

theorem map_path root mapping tree (spec : TreeSpec root mapping tree) vpn ppn permission
    (found : mapping[vpn]? = some (ppn, permission)) :
    ∃ p2 p1 a d, PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission a d) := by
  simpa only [found] using spec.2 vpn

theorem absent_path root mapping tree (spec : TreeSpec root mapping tree) vpn
    (absent : mapping[vpn]? = none) : PtTree.Blocks tree vpn := by
  simpa only [absent] using spec.2 vpn

/-- The snapshot fixes the root and all upper raw words. Its leaf remains
an existential A/D variant, not the invariant's current physical value. -/
theorem snapshot_path root mapping tree snapshot (spec : TreeSpec root mapping tree)
    (same : PtTree.canon tree = PtTree.canon snapshot) vpn ppn permission
    (found : mapping[vpn]? = some (ppn, permission)) :
    PtTree.base snapshot = root ∧ ∃ p2 p1 a d,
      PtTree.Maps snapshot vpn p2 p1 (KptLeaf.word ppn permission a d) := by
  have bases := congrArg PtTree.base same
  change PtTree.base tree = PtTree.base snapshot at bases
  refine ⟨bases.symm.trans spec.1, ?_⟩
  obtain ⟨p2,p1,a,d,mapped⟩ := map_path root mapping tree spec vpn ppn permission found
  obtain ⟨q0,qmapped,canonical⟩ := PtTree.maps_across tree snapshot vpn p2 p1 _ same mapped
  have canonical' : PteCanonical.canon q0 = PteCanonical.canon (KptLeaf.word ppn permission false false) := by
    rw [canonical, KptLeaf.word_canonical, KptLeaf.word_canonical]
  obtain ⟨a',d',word⟩ := Sv39Walk.leaf_variant ppn permission q0 canonical'
  exact ⟨p2,p1,a',d',word ▸ qmapped⟩

/-- The complete map/absent-map specification survives an A/D-only update
at a mapped path. No claim is made that canonicalization preserves arbitrary
invalid nonleaf words at level zero. -/
theorem set_leaf_spec root mapping tree (spec : TreeSpec root mapping tree)
    vpn p2 p1 p0 (mapped : PtTree.Maps tree vpn p2 p1 p0) a d :
    TreeSpec root mapping (PtTree.setLeaf tree vpn (PteCanonical.setAD p0 a d)) := by
  constructor
  · obtain ⟨c1,c0,hc1,hc0,_⟩ := mapped
    simpa only [PtTree.setLeaf, hc1, hc0, PtTree.base_updateChild] using spec.1
  intro query
  cases found : mapping[query]? with
  | none =>
    exact PtTree.set_leaf_blocks tree vpn query p2 p1 p0 _ mapped (absent_path root mapping tree spec query found)
  | some value =>
    rcases value with ⟨ppn,permission⟩
    obtain ⟨q2,q1,qa,qd,qmapped⟩ := map_path root mapping tree spec query ppn permission found
    by_cases eq : query = vpn
    · subst query
      obtain ⟨rfl,rfl,word⟩ := PtTree.maps_det tree vpn p2 p1 p0 q2 q1 _ mapped qmapped
      obtain ⟨aa,dd,updated⟩ := Sv39Walk.leaf_variant ppn permission (PteCanonical.setAD p0 a d) (by
        rw [PteCanonical.canon_variant, word, KptLeaf.word_canonical, KptLeaf.word_canonical])
      refine ⟨p2,p1,aa,dd,?_⟩
      rw [← updated]
      rcases mapped with ⟨c1,c0,hc1,hc0,hp2,hp1,hp0,hb1,hb0,hv2,hn2,hv1,hn1,hv0,hl0,hn0,hpb0⟩
      apply PtTree.set_leaf_maps_self tree vpn p2 p1 p0 _
        ⟨c1,c0,hc1,hc0,hp2,hp1,hp0,hb1,hb0,hv2,hn2,hv1,hn1,hv0,hl0,hn0,hpb0⟩
      · exact (PtTree.set_ad_valid_leaf p0 a d hl0).mpr hv0
      · exact (PtTree.leaf_setAD p0 a d).mpr hl0
      · simpa only [PtTree.NoNapot, PtTree.ext_setAD] using hn0
      · simpa only [PtTree.PbmtZero, PtTree.ext_setAD] using hpb0
    · exact ⟨q2,q1,qa,qd,PtTree.set_leaf_maps_other tree vpn query q2 q1 _ _ eq qmapped⟩

end Xv6.Kernel.KptShared
