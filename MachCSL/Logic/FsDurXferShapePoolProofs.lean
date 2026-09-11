import MachCSL.Logic.FsDurXferShapeInodeProofs
import MachCSL.Logic.FsStateBitmapProofs

namespace MachCSL.Logic.FsDurXferShape
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurXferRuns

private theorem pool_insert_lookup (pool : BlockMap) b bytes a :
    (PartialMap.insert (M := Disk.ImageMap) pool b bytes)[a]? = if b = a then some bytes else pool[a]? := LawfulPartialMap.get?_insert (M := Disk.ImageMap) (m := pool) (k := b) (k' := a) (v := bytes)
private theorem pool_delete_lookup (pool : BlockMap) b a :
    (PartialMap.delete (M := Disk.ImageMap) pool b)[a]? = if b = a then none else pool[a]? := LawfulPartialMap.get?_delete (M := Disk.ImageMap) (m := pool) (k := b) (k' := a)

theorem poolPM_empty used : PoolPM [] used ∅ := by
  constructor
  · intro b; simp
  · intro b bytes get; simp at get

theorem poolPM_used_cons b indices used pool (usedB : b ∈ used) :
    PoolPM (b :: indices) used pool ↔ PoolPM indices used pool := by
  have domains : ∀ a : Int, (a ∈ b :: indices ∧ a ∉ used) ↔ (a ∈ indices ∧ a ∉ used) := by
    intro a
    by_cases same : a = b
    · subst a; simp [usedB]
    · simp [List.mem_cons, same]
  constructor
  · intro h; exact ⟨fun a => (h.domain a).trans (domains a), h.length⟩
  · intro h; exact ⟨fun a => (h.domain a).trans (domains a).symm, h.length⟩

theorem poolPM_absent b indices used pool (pm : PoolPM indices used pool) (absent : b ∉ indices) : pool[b]? = none := by
  cases found : pool[b]? with
  | none => rfl
  | some bytes => exact False.elim (absent ((pm.domain b).mp (by simp [found])).1)

theorem poolPM_insert b indices used pool bytes (pm : PoolPM indices used pool)
    (unused : b ∉ used) (length : bytes.length = 1024) :
    PoolPM (b :: indices) used (PartialMap.insert (M := Disk.ImageMap) pool b bytes) := by
  constructor
  · intro a
    rw [pool_insert_lookup]
    by_cases same : b = a
    · subst a; simp [unused]
    · simp only [if_neg same, List.mem_cons, Ne.symm same, false_or]
      exact pm.domain a
  · intro a value get
    rw [pool_insert_lookup] at get
    split at get
    · have eq := Option.some.inj get; subst value; exact length
    · exact pm.length a value get

theorem poolPM_delete b indices used pool (pm : PoolPM (b :: indices) used pool)
    (absent : b ∉ indices) : PoolPM indices used (PartialMap.delete (M := Disk.ImageMap) pool b) := by
  constructor
  · intro a
    rw [pool_delete_lookup]
    by_cases same : b = a
    · subst a; simp [absent]
    · simp only [if_neg same]
      simpa only [List.mem_cons, Ne.symm same, false_or] using pm.domain a
  · intro a bytes get
    rw [pool_delete_lookup] at get
    split at get
    · contradiction
    · exact pm.length a bytes get

variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem free_pool_list_pm used indices (nodup : indices.Nodup) :
    bigSepL (fun _ b => FsState.poolElt view used b) indices ⊢
      ∃ pool, ⌜PoolPM indices used pool⌝ ∗
        bigSepM (M := Disk.ImageMap) (fun b bytes => FsView.blockOwned view b bytes) pool := by
  induction indices with
  | nil =>
    iintro _
    iexists (∅ : BlockMap)
    isplit
    · ipureintro; exact poolPM_empty used
    · rw [BigSepM.bigSepM_empty.to_eq]; iempintro
  | cons b indices ih =>
    obtain ⟨absent, tailNodup⟩ := List.nodup_cons.mp nodup
    rw [BigSepL.bigSepL_cons.to_eq]
    iintro ⟨Hb, Htail⟩
    ihave ⟨%pool, %pm, Hpool⟩ := ih tailNodup $$ Htail
    by_cases usedB : b ∈ used
    · iexists pool
      iframe Hpool
      ipureintro
      exact (poolPM_used_cons b indices used pool usedB).mpr pm
    · rw [FsState.poolElt_free view used b usedB]
      icases Hb with ⟨%bytes, Hb⟩
      ihave %length := FsView.blockOwned_length view b bytes $$ Hb
      have noKey : get? (M := Disk.ImageMap) pool b = none := poolPM_absent b indices used pool pm absent
      iexists PartialMap.insert (M := Disk.ImageMap) pool b bytes
      isplit
      · ipureintro; exact poolPM_insert b indices used pool bytes pm usedB length
      · rw [(BigSepM.bigSepM_insert (M := Disk.ImageMap) noKey).to_eq]
        iframe Hb Hpool

theorem free_pool_list_of_pm used indices pool (nodup : indices.Nodup) (pm : PoolPM indices used pool) :
    bigSepM (M := Disk.ImageMap) (fun b bytes => FsView.blockOwned view b bytes) pool ⊢
      bigSepL (fun _ b => FsState.poolElt view used b) indices := by
  induction indices generalizing pool with
  | nil => rw [BigSepL.bigSepL_nil.to_eq]; iintro _; iempintro
  | cons b indices ih =>
    obtain ⟨absent, tailNodup⟩ := List.nodup_cons.mp nodup
    rw [BigSepL.bigSepL_cons.to_eq]
    iintro Hpool
    by_cases usedB : b ∈ used
    · rw [FsState.poolElt_used view used b usedB]
      isplit
      · iempintro
      · iapply ih pool tailNodup ((poolPM_used_cons b indices used pool usedB).mp pm) $$ Hpool
    · have present : (pool[b]?).isSome := (pm.domain b).mpr ⟨List.mem_cons_self, usedB⟩
      obtain ⟨bytes, found⟩ := Option.isSome_iff_exists.mp present
      ihave ⟨Hb, Hrest⟩ := (BigSepM.bigSepM_delete (M := Disk.ImageMap) found).mp $$ Hpool
      rw [FsState.poolElt_free view used b usedB]
      isplitl [Hb]
      · iexists bytes; iexact Hb
      · iapply ih (PartialMap.delete (M := Disk.ImageMap) pool b) tailNodup
          (poolPM_delete b indices used pool pm absent) $$ Hrest

theorem pool_pm_runs pool (lengths : ∀ (b : Int) bytes, pool[b]? = some bytes → bytes.length = 1024) :
    bigSepM (M := Disk.ImageMap) (fun b bytes => FsView.blockOwned view b bytes) pool ⊣⊢ phiRuns view (poolRuns pool) := by
  unfold poolRuns phiRuns
  rw [BigSepL.bigSepL_map, BigSepM.bigSepM_toList.to_eq]
  apply BIBase.BiEntails.of_eq
  apply BigSepL.bigSepL_eq
  intro k entry found
  apply BIBase.BiEntails.to_eq
  have get := (LawfulFiniteMap.toList_get (M := Disk.ImageMap) (m := pool) (k := entry.1) (v := entry.2)).mp (List.mem_of_getElem? found)
  simp only [runBlock, runOffset, runBytes]
  unfold FsView.blockOwned
  constructor
  · iintro ⟨_, H⟩; iexact H
  · iintro H; iframe H; ipureintro; exact lengths entry.1 entry.2 get

theorem poolIndices_nodup nb : (FsState.poolIndices nb).Nodup := by
  unfold FsState.poolIndices
  exact List.nodup_range.map Int.ofNat (fun a b ne eq => ne (Int.ofNat.inj eq))

theorem free_pool_runs nb used : FsState.freePool view nb used ⊢
    ∃ pool, ⌜PoolPM (FsState.poolIndices nb) used pool⌝ ∗ phiRuns view (poolRuns pool) := by
  unfold FsState.freePool
  iintro H
  ihave ⟨%pool, %pm, Hpool⟩ := free_pool_list_pm view used (FsState.poolIndices nb) (poolIndices_nodup nb) $$ H
  iexists pool
  isplit
  · ipureintro; exact pm
  · iapply (pool_pm_runs view pool pm.length).mp $$ Hpool

theorem free_pool_of_runs nb used pool (pm : PoolPM (FsState.poolIndices nb) used pool) :
    phiRuns view (poolRuns pool) ⊢ FsState.freePool view nb used := by
  iintro H
  ihave H := (pool_pm_runs view pool pm.length).mpr $$ H
  unfold FsState.freePool
  iapply free_pool_list_of_pm view used (FsState.poolIndices nb) pool (poolIndices_nodup nb) pm $$ H

end MachCSL.Logic.FsDurXferShape
