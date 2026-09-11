import MachCSL.Logic.KptGhostSpec
import MachCSL.Logic.TsoViewsProofs
import Xv6.Kernel.PtTreeLink

namespace MachCSL.Logic.KptGhost
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

instance treePending_exclusive : Exclusive treePending := by unfold treePending; infer_instance
instance treeShot_coreId t : CoreId (treeShot t) := by unfold treeShot; infer_instance
instance boundPending_exclusive : Exclusive boundPending := by unfold boundPending; infer_instance
instance boundShot_coreId B : CoreId (boundShot B) := by unfold boundShot; infer_instance

theorem treePending_valid : ✓ treePending := trivial
theorem treeShot_valid (t : Tree) : ✓ treeShot t := Agree.toAgree_valid
theorem boundPending_valid : ✓ boundPending := trivial
theorem boundShot_valid (B : Nat) : ✓ boundShot B := Agree.toAgree_valid

theorem tree_update (t : Tree) : treePending ~~> treeShot t := Update.exclusive (treeShot_valid t)
theorem bound_update (B : Nat) : boundPending ~~> boundShot B := Update.exclusive (boundShot_valid B)
theorem tree_agreement (t t' : Tree) (valid : ✓ (treeShot t • treeShot t')) :
    Xv6.Kernel.PtTree.canon t = Xv6.Kernel.PtTree.canon t' := by
  have equal : (⟨Xv6.Kernel.PtTree.canon t⟩ : DiscreteO Tree) = ⟨Xv6.Kernel.PtTree.canon t'⟩ :=
    toAgree_op_valid_iff_eq.mp valid
  exact congrArg DiscreteO.car equal

theorem bound_agreement (B B' : Nat) (valid : ✓ (boundShot B • boundShot B')) : B = B' := by
  have equal : (⟨B⟩ : DiscreteO Nat) = ⟨B'⟩ := toAgree_op_valid_iff_eq.mp valid
  exact congrArg DiscreteO.car equal

theorem tree_pending_invalid : ¬ ✓ (treePending • treePending) := id
theorem tree_pending_shot_invalid t : ¬ ✓ (treePending • treeShot t) := id
theorem bound_pending_invalid : ¬ ✓ (boundPending • boundPending) := id
theorem bound_pending_shot_invalid B : ¬ ✓ (boundPending • boundShot B) := id

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance mapAuth_timeless γ M : Timeless (mapAuth capacity γ M) := by
  letI := capacity.mapping
  unfold mapAuth
  infer_instance
instance mapAt_timeless γ vpn ppn pc : Timeless (mapAt capacity γ vpn ppn pc) := by
  letI := capacity.mapping
  unfold mapAt
  infer_instance
instance mapAt_persistent γ vpn ppn pc : Persistent (mapAt capacity γ vpn ppn pc) := by
  letI := capacity.mapping
  unfold mapAt
  infer_instance
instance allClaims_timeless γ M : Timeless (allClaims capacity γ M) := by
  unfold allClaims
  infer_instance
instance allClaims_persistent γ M : Persistent (allClaims capacity γ M) := by
  unfold allClaims
  infer_instance
instance unset_timeless γ : Timeless (unset capacity γ) := by unfold unset; infer_instance
instance snapshot_timeless γ t : Timeless (snapshot capacity γ t) := by unfold snapshot; infer_instance
instance snapshot_persistent γ t : Persistent (snapshot capacity γ t) := by unfold snapshot; infer_instance
instance boundUnset_timeless γ : Timeless (boundUnset capacity γ) := by unfold boundUnset; infer_instance
instance bound_timeless γ logName B : Timeless (bound capacity γ logName B) := by unfold bound; infer_instance
instance bound_persistent γ logName B : Persistent (bound capacity γ logName B) := by unfold bound; infer_instance

theorem map_lookup γ M vpn ppn pc :
    iprop(mapAuth capacity γ M ∗ mapAt capacity γ vpn ppn pc ⊢ ⌜M[vpn]? = some (ppn, pc)⌝) := by
  letI := capacity.mapping
  unfold mapAuth mapAt
  iintro ⟨Ha,Hf⟩
  iapply ghost_map_lookup (H := KeyMap) (GF := GF) $$ Ha Hf

theorem map_agree γ vpn p p' pc pc' :
    iprop(mapAt capacity γ vpn p pc ∗ mapAt capacity γ vpn p' pc' ⊢ ⌜p = p' ∧ pc = pc'⌝) := by
  letI := capacity.mapping
  unfold mapAt
  iintro ⟨Hl,Hr⟩
  ihave %eq := ghost_map_elem_agree (H := KeyMap) (GF := GF) γ vpn .discard .discard (p, pc) (p', pc')
    $$ [$Hl $Hr]
  ipureintro
  exact Prod.mk.inj eq

theorem map_insert γ M vpn ppn pc (fresh : M[vpn]? = none) :
    iprop(mapAuth capacity γ M ⊢ |==>
      (mapAuth capacity γ (M.insert vpn (ppn, pc)) ∗ mapAt capacity γ vpn ppn pc)) := by
  letI := capacity.mapping
  have eq : Iris.Std.PartialMap.insert (M := KeyMap) M vpn (ppn, pc) = M.insert vpn (ppn, pc) := by
    apply _root_.Std.ExtTreeMap.ext_getElem?
    intro key
    simp [Iris.Std.insert, _root_.Std.ExtTreeMap.getElem?_alter, _root_.Std.ExtTreeMap.getElem?_insert]
  rw [← eq]
  unfold mapAuth mapAt
  iintro Ha
  iapply ghost_map_insert_persist (H := KeyMap) (GF := GF) vpn (ppn, pc) fresh $$ Ha

theorem persist_all γ (M : Map) :
    letI := capacity.mapping
    iprop((bigSepM (M := KeyMap) (fun vpn value =>
      ghost_map_elem (H := KeyMap) γ (.own 1) vpn value) M : IProp GF) ⊢ |==> allClaims capacity γ M) := by
  letI := capacity.mapping
  unfold allClaims
  apply Entails.trans ?_ (BigSepM.bigSepM_bupd _)
  apply BigSepM.bigSepM_mono
  intro vpn value found
  unfold mapAt
  iintro H
  iapply ghost_map_elem_persist (H := KeyMap) (GF := GF) γ vpn (.own 1) value $$ H

theorem allocate_map (M : Map) (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ γ, mapAuth capacity γ M ∗ allClaims capacity γ M ∗ frame) := by
  letI := capacity.mapping
  iintro HR
  imod ghost_map_alloc (H := KeyMap) (GF := GF) M with ⟨%γ, Ha, Hf⟩
  imod persist_all capacity γ M $$ Hf with Hf
  imodintro
  iexists γ
  unfold mapAuth
  iframe Ha Hf HR

theorem claim_lookup γ M vpn ppn pc (found : M[vpn]? = some (ppn, pc)) :
    iprop(allClaims capacity γ M ⊢ mapAt capacity γ vpn ppn pc) := by
  let Φ : VPN → Mapping → IProp GF := fun key value => mapAt capacity γ key value.1 value.2
  have h : Iris.Std.get? M vpn = some (ppn, pc) := found
  have lookup := BigSepM.bigSepM_lookup (PROP := IProp GF) (M := KeyMap)
    (Φ := Φ) (m := M) (i := vpn) (x := (ppn, pc)) h
  exact lookup


theorem shoot γ t : iprop(unset capacity γ ⊢ |==> snapshot capacity γ t) :=
  iOwn_update (E := capacity.tree) (tree_update t)

theorem agree γ t t' : iprop(snapshot capacity γ t ∗ snapshot capacity γ t' ⊢
    ⌜Xv6.Kernel.PtTree.canon t = Xv6.Kernel.PtTree.canon t'⌝) := by
  unfold snapshot
  iintro ⟨Hl,Hr⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.tree) $$ [$Hl $Hr]
  ipureintro
  exact tree_agreement t t' valid

theorem canonical γ t t' (same : Xv6.Kernel.PtTree.canon t = Xv6.Kernel.PtTree.canon t') :
    iprop(snapshot capacity γ t ⊢ snapshot capacity γ t') := by
  unfold snapshot treeShot
  rw [same]

theorem unset_exclusive γ : iprop(unset capacity γ ∗ unset capacity γ ⊢ False) := by
  unfold unset
  iintro ⟨Hl,Hr⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.tree) $$ [$Hl $Hr]
  exact (tree_pending_invalid valid).elim

theorem unset_snapshot_exclusive γ t : iprop(unset capacity γ ∗ snapshot capacity γ t ⊢ False) := by
  unfold unset snapshot
  iintro ⟨Hl,Hr⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.tree) $$ [$Hl $Hr]
  exact (tree_pending_shot_invalid t valid).elim

theorem allocate_unset (frame : IProp GF) : iprop(frame ⊢ |==> ∃ γ, unset capacity γ ∗ frame) := by
  iintro HR
  imod iOwn_alloc (E := capacity.tree) treePending treePending_valid with ⟨%γ,H⟩
  imodintro
  iexists γ
  unfold unset
  iframe H HR

theorem shoot_bound γ logName B :
    iprop(Tso.Views.llb capacity.views logName B ∗ boundUnset capacity γ ⊢ |==> bound capacity γ logName B) := by
  unfold boundUnset bound
  iintro ⟨Hlb,H⟩
  imod iOwn_update (E := capacity.bound) (bound_update B) $$ H with H
  imodintro
  iframe H Hlb

theorem bound_log γ logName B : iprop(bound capacity γ logName B ⊢ Tso.Views.llb capacity.views logName B) := by
  unfold bound
  iintro ⟨_,H⟩
  iexact H

theorem bound_agree γ logName logName' B B' :
    iprop(bound capacity γ logName B ∗ bound capacity γ logName' B' ⊢ ⌜B = B'⌝) := by
  unfold bound
  iintro ⟨⟨Hl,_⟩,⟨Hr,_⟩⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.bound) $$ [$Hl $Hr]
  ipureintro
  exact bound_agreement B B' valid

theorem bound_unset_exclusive γ : iprop(boundUnset capacity γ ∗ boundUnset capacity γ ⊢ False) := by
  unfold boundUnset
  iintro ⟨Hl,Hr⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.bound) $$ [$Hl $Hr]
  exact (bound_pending_invalid valid).elim

theorem bound_unset_shot_exclusive γ logName B :
    iprop(boundUnset capacity γ ∗ bound capacity γ logName B ⊢ False) := by
  unfold boundUnset bound
  iintro ⟨Hl,⟨Hr,_⟩⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.bound) $$ [$Hl $Hr]
  exact (bound_pending_shot_invalid B valid).elim

theorem allocate_bound_unset (frame : IProp GF) : iprop(frame ⊢ |==> ∃ γ, boundUnset capacity γ ∗ frame) := by
  iintro HR
  imod iOwn_alloc (E := capacity.bound) boundPending boundPending_valid with ⟨%γ,H⟩
  imodintro
  iexists γ
  unfold boundUnset
  iframe H HR

theorem allocate logName M (frame : IProp GF) : iprop(frame ⊢ |==> ∃ names,
    ⌜names.logLength = logName⌝ ∗ initial capacity names M ∗ frame) := by
  iintro HR
  imod allocate_map capacity M frame $$ HR with ⟨%γm,Hm,Hc,HR⟩
  imod allocate_unset capacity frame $$ HR with ⟨%γt,Ht,HR⟩
  imod allocate_bound_unset capacity frame $$ HR with ⟨%γb,Hb,HR⟩
  imodintro
  iexists Names.mk γm γt γb logName
  unfold initial
  iframe Hm Hc Ht Hb HR
  ipureintro
  rfl

theorem map_insert_frame γ M vpn ppn pc (fresh : M[vpn]? = none) (frame : IProp GF) :
    iprop(mapAuth capacity γ M ∗ frame ⊢ |==>
      (mapAuth capacity γ (M.insert vpn (ppn, pc)) ∗ mapAt capacity γ vpn ppn pc ∗ frame)) := by
  iintro ⟨Ha,HR⟩
  imod map_insert capacity γ M vpn ppn pc fresh $$ Ha with ⟨Ha,Hc⟩
  imodintro
  iframe Ha Hc HR

theorem shoot_frame γ t (frame : IProp GF) :
    iprop(unset capacity γ ∗ frame ⊢ |==> (snapshot capacity γ t ∗ frame)) := by
  iintro ⟨H,HR⟩
  imod shoot capacity γ t $$ H with H
  imodintro
  iframe H HR

theorem shoot_bound_frame γ logName B (frame : IProp GF) :
    iprop(Tso.Views.llb capacity.views logName B ∗ boundUnset capacity γ ∗ frame ⊢
      |==> (bound capacity γ logName B ∗ frame)) := by
  iintro ⟨Hlb,H,HR⟩
  imod shoot_bound capacity γ logName B $$ [$Hlb $H] with H
  imodintro
  iframe H HR

/-- The existing authority is essential: agreement alone cannot bound B by
an actual log length. The receipt uses the same supplied log name/capacity. -/
theorem bound_valid γ logName dq n B :
    iprop(Tso.Views.natAuth capacity.views logName dq n ∗ bound capacity γ logName B ⊢ ⌜B ≤ n⌝) := by
  unfold bound
  iintro ⟨Ha,⟨_,Hlb⟩⟩
  iapply Tso.Views.llb_valid capacity.views logName dq n B $$ Ha Hlb

/-- A logical re-close after the exact pure mapped-leaf A/D update requires
no ghost update. Physical ownership and actual write permission remain separate. -/
theorem snapshot_set_leaf γ (t : Tree) vpn p2 p1 p0 a d
    (mapped : Xv6.Kernel.PtTree.Maps t vpn p2 p1 p0) :
    iprop(snapshot capacity γ t ⊢ snapshot capacity γ
      (Xv6.Kernel.PtTree.setLeaf t vpn (MachCSL.Machine.PteCanonical.setAD p0 a d))) :=
  canonical capacity γ _ _ (Xv6.Kernel.PtTree.canon_set_leaf t vpn p2 p1 p0 a d mapped).symm

theorem actual : Spec capacity where
  mapLookup := map_lookup capacity
  mapAgree := map_agree capacity
  mapInsert := map_insert capacity
  allocateMap := allocate_map capacity
  claimLookup := claim_lookup capacity
  shoot := shoot capacity
  agree := agree capacity
  canonical := canonical capacity
  unsetExclusive := unset_exclusive capacity
  unsetSnapshotExclusive := unset_snapshot_exclusive capacity
  allocateUnset := allocate_unset capacity
  shootBound := shoot_bound capacity
  boundLog := bound_log capacity
  boundAgree := bound_agree capacity
  boundUnsetExclusive := bound_unset_exclusive capacity
  boundUnsetShotExclusive := bound_unset_shot_exclusive capacity
  allocateBoundUnset := allocate_bound_unset capacity
  allocate := allocate capacity

end MachCSL.Logic.KptGhost
