import MachCSL.Logic.IcacheTopRegistryPureProofs
import MachCSL.Logic.FsTopProofs
import MachCSL.Logic.LogTxProofs

namespace MachCSL.Logic.IcacheTopRegistry
open Iris Iris.Std Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)

instance armAuth_timeless arms : Timeless (armAuth capacity names arms) := by
  letI := capacity.arms
  unfold armAuth
  infer_instance
instance parked_timeless entry : Timeless (parked capacity names entry) := by unfold parked; infer_instance
instance armed_timeless k t q S : Timeless (armed capacity names k t q S) := by
  letI := capacity.arms
  unfold armed
  infer_instance
instance parkedMap_timeless arms : Timeless (parkedMap capacity names arms) := by unfold parkedMap; infer_instance
instance body_timeless : Timeless (body capacity names) := by unfold body; infer_instance

/-- Separate same-world configuration-camera allocation; the invariant allocator
below consumes a supplied authority and does not invoke this constructor. -/
theorem allocate_empty (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ γ, armAuth capacity {names with arms := γ} ∅ ∗ frame) := by
  letI := capacity.arms
  iintro Hframe
  imod (ghost_map_alloc_empty (H := ArmMap) (K := Nat) (V := Entry)) with ⟨%γ, Ha⟩
  imodintro
  iexists γ
  unfold armAuth
  iframe

theorem armed_lookup arms k t q S :
    iprop(⊢ armAuth capacity names arms -∗ armed capacity names k t q S -∗
      ⌜get? arms k = some ((t,q),S)⌝) := by
  letI := capacity.arms
  exact ghost_map_lookup

theorem parked_empty_of_no_ops (arms : ArmMap Entry) :
    iprop(⊢ LogTx.auth capacity.transactions names.transactions ∅ -∗ parkedMap capacity names arms -∗ ⌜arms = ∅⌝) := by
  iintro Ha Hpark
  ihave %empty : ⌜∀ k : Nat, get? arms k = none⌝ $$ [Ha Hpark]
  · iapply pure_forall.mpr
    iintro %k
    cases found : get? arms k with
    | none => ipureintro; rfl
    | some entry =>
      iunfold parkedMap at Hpark
      ihave Hp := BigSepM.bigSepM_lookup found $$ Hpark
      iunfold parked at Hp
      ihave %bad := LogTx.tx_pin_no_ops capacity.transactions names.transactions entry.1.1 entry.1.2 $$ Ha Hp
      exact bad.elim
  · ipureintro
    apply LawfulPartialMap.equiv_iff_eq.mp
    intro k
    rw [empty k, get?_empty]

variable {hlc : HasLC} [InvGS_gen hlc GF]

instance invariant_persistent N : Persistent (invariant capacity names N) := by unfold invariant; infer_instance

theorem allocate (N : Namespace) (E : CoPset) (nodes : Xv6.Fs.DurableState.InodeMap)
    (localNodes : ∀ i node, nodes[i]? = some node → Xv6.Fs.DurableNode.Local i node) :
    iprop(⊢ FsTop.auth capacity.top names.top nodes -∗ armAuth capacity names ∅
      ={E}=∗ invariant capacity names N) := by
  iintro Ha Hl
  unfold invariant
  iapply inv_alloc
  iintro !>
  unfold body
  iexists nodes, (∅ : ArmMap Entry)
  iframe Ha Hl
  isplit
  · unfold parkedMap
    simp
    exact .rfl
  · ipureintro
    exact clean_empty nodes localNodes

open scoped Classical in
theorem arm (N : Namespace) (E : CoPset) (i : Int) (t : Nat) (q : Qp)
    (mask : (↑N : CoPset) ⊆ E) :
    iprop(⊢ invariant capacity names N -∗ LogTx.tx_pin capacity.transactions names.transactions t q
      ={E}=∗ ∃ k, armed capacity names k t q {i}) := by
  letI := capacity.arms
  iintro #Hi Ht
  iunfold invariant at Hi
  imod inv_acc mask $$ Hi with ⟨Hb, Hclose⟩
  imod Hb
  iunfold body at Hb
  icases Hb with ⟨%nodes, %arms, Ha, Hl, Hp, %hc⟩
  let k : Nat := Iris.Std.Heap.fresh (M := ArmMap) (m := arms) True.intro
  have fresh : get? arms k = none := Iris.Std.Heap.get?_fresh (M := ArmMap) (m := arms) (H := True.intro)
  iunfold armAuth at Hl
  imod ghost_map_insert k ((t,q),({i} : InumSet)) fresh $$ Hl with ⟨Hl, Hr⟩
  imod Hclose $$ [Ha Hl Hp Ht] with _
  · iintro !>
    unfold body
    iexists nodes, (PartialMap.insert arms k ((t,q),({i} : InumSet)))
    unfold armAuth
    iframe Ha Hl
    isplit
    · unfold parkedMap
      iapply (BigSepM.bigSepM_insert fresh).mpr
      unfold parked
      iframe
    · ipureintro
      exact clean_insert nodes arms k _ fresh hc
  · imodintro
    iexists k
    unfold armed
    iexact Hr

theorem disarm (N : Namespace) (E : CoPset) (k t : Nat) (q : Qp) (S : InumSet) (i : Int) (node : FsTop.Node)
    (mask : (↑N : CoPset) ⊆ E) (localNode : Xv6.Fs.DurableNode.Local i node) :
    iprop(⊢ invariant capacity names N -∗ armed capacity names k t q S -∗
      FsTop.frag capacity.top names.top i node ={E}=∗
      armed capacity names k t q (S \ {i}) ∗ FsTop.frag capacity.top names.top i node) := by
  letI := capacity.arms
  iintro #Hi Hr Hf
  iunfold invariant at Hi
  imod inv_acc mask $$ Hi with ⟨Hb, Hclose⟩
  imod Hb
  iunfold body at Hb
  icases Hb with ⟨%nodes, %arms, Ha, Hl, Hp, %hc⟩
  ihave %entry := armed_lookup capacity names arms k t q S $$ Hl Hr
  iunfold FsTop.frag at Hf
  ihave %nodeAt := FsTop.lookup capacity.top names.top nodes (.own 1) i node $$ Ha Hf
  iunfold armAuth at Hl
  iunfold armed at Hr
  imod ghost_map_update ((t,q), S \ {i}) $$ Hl Hr with ⟨Hl, Hr⟩
  imod Hclose $$ [Ha Hl Hp] with _
  · iintro !>
    unfold body
    iexists nodes, (PartialMap.insert arms k ((t,q),S \ {i}))
    unfold armAuth
    iframe Ha Hl
    isplit
    · unfold parkedMap
      iapply BigSepM.bigSepM_insert_delete.mpr
      ihave Hp := (BigSepM.bigSepM_delete entry).mp $$ Hp
      isimp only [parked] at Hp
      unfold parked
      iexact Hp
    · ipureintro
      exact clean_disarm nodes arms k t q S i node entry nodeAt localNode hc
  · imodintro
    unfold armed FsTop.frag
    iframe Hr Hf

theorem release (N : Namespace) (E : CoPset) (k t : Nat) (q : Qp)
    (mask : (↑N : CoPset) ⊆ E) :
    iprop(⊢ invariant capacity names N -∗ armed capacity names k t q ∅
      ={E}=∗ LogTx.tx_pin capacity.transactions names.transactions t q) := by
  letI := capacity.arms
  iintro #Hi Hr
  iunfold invariant at Hi
  imod inv_acc mask $$ Hi with ⟨Hb, Hclose⟩
  imod Hb
  iunfold body at Hb
  icases Hb with ⟨%nodes, %arms, Ha, Hl, Hp, %hc⟩
  ihave %entry := armed_lookup capacity names arms k t q ∅ $$ Hl Hr
  iunfold parkedMap at Hp
  ihave ⟨Ht, Hp⟩ := (BigSepM.bigSepM_delete entry).mp $$ Hp
  iunfold armAuth at Hl
  iunfold armed at Hr
  imod ghost_map_delete k ((t,q),(∅ : InumSet)) $$ Hl Hr with Hl
  imod Hclose $$ [Ha Hl Hp] with _
  · iintro !>
    unfold body
    iexists nodes, (PartialMap.delete arms k)
    unfold armAuth parkedMap
    iframe Ha Hl Hp
    ipureintro
    exact clean_release nodes arms k t q entry hc
  · imodintro
    iunfold parked at Ht
    iexact Ht

theorem clean_access (N : Namespace) (E : CoPset) (mask : (↑N : CoPset) ⊆ E) :
    iprop(⊢ invariant capacity names N -∗ LogTx.auth capacity.transactions names.transactions ∅
      ={E, E \ ↑N}=∗ ∃ nodes,
      FsTop.auth capacity.top names.top nodes ∗
      ⌜∀ i node, nodes[i]? = some node → Xv6.Fs.DurableNode.Local i node⌝ ∗
      LogTx.auth capacity.transactions names.transactions ∅ ∗
      (FsTop.auth capacity.top names.top nodes ={E \ ↑N, E}=∗ True)) := by
  iintro #Hi Htx
  iunfold invariant at Hi
  imod inv_acc mask $$ Hi with ⟨Hb, Hclose⟩
  imod Hb
  iunfold body at Hb
  icases Hb with ⟨%nodes, %arms, Ha, Hl, Hp, %hc⟩
  ihave %empty := parked_empty_of_no_ops capacity names arms $$ Htx Hp
  subst arms
  imodintro
  iexists nodes
  iframe Ha Htx
  isplit
  · ipureintro
    exact clean_empty_local nodes hc
  · iintro Ha
    iapply Hclose
    iintro !>
    unfold body
    iexists nodes, (∅ : ArmMap Entry)
    iframe Ha Hl Hp
    ipureintro
    exact hc

theorem actual : Spec capacity :=
  ⟨fun names => allocate capacity names, fun names => arm capacity names,
    fun names => disarm capacity names, fun names => release capacity names,
    fun names => clean_access capacity names⟩

end MachCSL.Logic.IcacheTopRegistry
