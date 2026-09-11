import MachCSL.Logic.FsDurAllocFootprintProofs

namespace MachCSL.Logic.FsDurAlloc
open Iris Iris.Std Xv6.Fs DurableState DurableNode

theorem metadata_of (state : State) (slot : Slot) (valid : Valid state slot)
    (isMetadata : metadataClass slot = true) : Metadata state (fpBlock state slot) := by
  cases slot with
  | sb => exact Or.inl rfl
  | bmap => exact Or.inr (Or.inl rfl)
  | record i => exact Or.inr (Or.inr ⟨i, valid, rfl⟩)
  | data | indirect | pool => cases isMetadata

theorem data_slot_range (state : State) disk (i : Int) (n : Node) (k : Nat)
    (bytes : Snapshot.Bytes state disk) (found : state.inodes[i]? = some n)
    (stored : n.blocks[k]?.isSome) : k < 268 ∧ n.address k ≠ 0 := by
  have repr := bytes.repr i n found
  have bound : k < 268 := by
    by_cases h : k < 268
    · exact h
    have absent := repr.top k (by omega)
    rw [absent] at stored
    cases stored
  exact ⟨bound, (repr.domain k bound).mp stored⟩

theorem pool_free (state : State) disk b (nonempty : fpBytes state disk (.pool b) ≠ []) : b ∉ state.used := by
  intro used
  exact nonempty (by simp only [fpBytes, if_pos used])

/-- Every nonempty nonmetadata slot is either a free-pool block or a
source node slot, with its original constructor recoverable from the witness. -/
theorem nonmetadata_role (state : State) disk slot (bytes : Snapshot.Bytes state disk)
    (valid : Valid state slot) (nonmeta : metadataClass slot = false)
    (nonempty : fpBytes state disk slot ≠ []) :
    (∃ b, slot = .pool b ∧ b ∉ state.used) ∨
      ∃ i n k, state.inodes[i]? = some n ∧ k ≤ 268 ∧ n.slot k ≠ 0 ∧
        fpBlock state slot = n.slot k ∧ n.Owns (fpBlock state slot) ∧
        slot = (if k = 268 then Slot.indirect i else Slot.data i k) := by
  cases slot with
  | sb | bmap | record => cases nonmeta
  | pool b => exact Or.inl ⟨b, rfl, pool_free state disk b nonempty⟩
  | data i k =>
    obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp valid.1
    have stored := valid.2
    rw [nodeAt_found state i n found] at stored
    obtain ⟨bound, nonzero⟩ := data_slot_range state disk i n k bytes found stored
    right
    refine ⟨i, n, k, found, by omega, ?_, ?_, ?_, ?_⟩
    · rwa [slot_data n k bound]
    · simp only [fpBlock, nodeAt_found state i n found, slot_data n k bound]
    · exact Or.inl ⟨k, stored, by simp only [fpBlock, nodeAt_found state i n found]⟩
    · simp only [if_neg (show k ≠ 268 by omega)]
  | indirect i =>
    obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp valid
    have nonzero : n.indirect ≠ 0 := by
      intro zero
      exact nonempty (by simp only [fpBytes, nodeAt_found state i n found, if_pos zero])
    right
    refine ⟨i, n, 268, found, by omega, ?_, ?_, ?_, ?_⟩
    · rwa [slot_indirect]
    · simp only [fpBlock, nodeAt_found state i n found, slot_indirect]
    · exact Or.inr ⟨nonzero, by simp only [fpBlock, nodeAt_found state i n found]⟩
    · simp only [↓reduceIte]

theorem metadata_nonmetadata_ne (state : State) disk x y (bytes : Snapshot.Bytes state disk)
    (validX : Valid state x) (validY : Valid state y)
    (isMetadata : metadataClass x = true) (nonmeta : metadataClass y = false)
    (nonempty : fpBytes state disk y ≠ []) : fpBlock state x ≠ fpBlock state y := by
  intro same
  have isMeta := metadata_of state x validX isMetadata
  rw [same] at isMeta
  rcases nonmetadata_role state disk y bytes validY nonmeta nonempty with ⟨b, rfl, free⟩ | ⟨i, n, k, found, _, _, _, own, _⟩
  · exact free (bytes.metadataUsed b isMeta)
  · exact (bytes.ownedUsed i n _ found own).2 isMeta

theorem nonmetadata_collision (state : State) disk x y (bytes : Snapshot.Bytes state disk)
    (validX : Valid state x) (validY : Valid state y)
    (nonmetaX : metadataClass x = false) (nonmetaY : metadataClass y = false)
    (nonemptyX : fpBytes state disk x ≠ []) (nonemptyY : fpBytes state disk y ≠ [])
    (same : fpBlock state x = fpBlock state y) : x = y := by
  rcases nonmetadata_role state disk x bytes validX nonmetaX nonemptyX with ⟨b, rfl, free⟩ | ⟨i, n, k, found, bound, nz, block, own, shape⟩
  · rcases nonmetadata_role state disk y bytes validY nonmetaY nonemptyY with ⟨c, rfl, _⟩ | ⟨j, m, l, get, _, _, _, own, _⟩
    · exact congrArg Slot.pool same
    · have used := (bytes.ownedUsed j m _ get own).1
      rw [← same] at used
      exact (free used).elim
  · rcases nonmetadata_role state disk y bytes validY nonmetaY nonemptyY with ⟨c, rfl, free⟩ | ⟨j, m, l, get, bound', _, block', own', shape'⟩
    · have used := (bytes.ownedUsed i n _ found own).1
      rw [same] at used
      exact (free used).elim
    · have ij : i = j := bytes.disjoint i n j m _ found get (same ▸ own) own'
      subst j
      have nm : n = m := Option.some.inj (found.symm.trans get)
      subst m
      have kl := bytes.slot i n found k l bound bound' nz (block.symm.trans (same.trans block'))
      rw [shape, shape', kl]

theorem fp_separated (state : State) disk x y (bytes : Snapshot.Bytes state disk)
    (validX : Valid state x) (validY : Valid state y) (different : x ≠ y)
    (nonemptyX : fpBytes state disk x ≠ []) (nonemptyY : fpBytes state disk y ≠ []) :
    fpBlock state x ≠ fpBlock state y ∨
      fpOffset x + (fpBytes state disk x).length ≤ (fpOffset y : Int) ∨
      fpOffset y + (fpBytes state disk y).length ≤ (fpOffset x : Int) := by
  cases mx : metadataClass x <;> cases my : metadataClass y
  · exact Or.inl fun same => different (nonmetadata_collision state disk x y bytes validX validY mx my nonemptyX nonemptyY same)
  · exact Or.inl (Ne.symm (metadata_nonmetadata_ne state disk y x bytes validY validX my mx nonemptyX))
  · exact Or.inl (metadata_nonmetadata_ne state disk x y bytes validX validY mx my nonemptyY)
  · cases x with
    | data | indirect | pool => cases mx
    | sb =>
      cases y with
      | data | indirect | pool => cases my
      | sb => exact (different rfl).elim
      | bmap => exact Or.inl (Snapshot.superblock_bitmap_distinct bytes)
      | record j =>
        obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp validY
        exact Or.inl (Snapshot.metadata_distinct bytes j n found).1
    | bmap =>
      cases y with
      | data | indirect | pool => cases my
      | sb => exact Or.inl (Ne.symm (Snapshot.superblock_bitmap_distinct bytes))
      | bmap => exact (different rfl).elim
      | record j =>
        obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp validY
        exact Or.inl (Snapshot.metadata_distinct bytes j n found).2
    | record i =>
      obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp validX
      cases y with
      | data | indirect | pool => cases my
      | sb => exact Or.inl (Ne.symm (Snapshot.metadata_distinct bytes i n found).1)
      | bmap => exact Or.inl (Ne.symm (Snapshot.metadata_distinct bytes i n found).2)
      | record j =>
        obtain ⟨m, get⟩ := Option.isSome_iff_exists.mp validY
        have len := dinodeBytes_length n.record (bytes.repr i n found).record
        have len' := dinodeBytes_length m.record (bytes.repr j m get).record
        have ne : i ≠ j := fun eq => different (congrArg Slot.record eq)
        simp only [fpBlock, fpOffset, fpBytes, nodeAt_found state i n found,
          nodeAt_found state j m get, len, len']
        omega

theorem fp_disjoint (state : State) disk x y (bytes : Snapshot.Bytes state disk)
    (validX : Valid state x) (validY : Valid state y) (different : x ≠ y) :
    PartialMap.disjoint (M := Disk.ImageMap) (fpMap state disk x) (fpMap state disk y) := by
  by_cases emptyX : fpBytes state disk x = []
  · simp only [fpMap, emptyX, fpRun_empty]
    exact LawfulPartialMap.disjoint_empty_left _
  by_cases emptyY : fpBytes state disk y = []
  · simp only [fpMap, emptyY, fpRun_empty]
    exact LawfulPartialMap.disjoint_empty_right _
  have ox := fp_ok state disk x bytes validX
  have oy := fp_ok state disk y bytes validY
  exact fpRun_disjoint _ _ _ _ _ _ ox.2.1 ox.2.2 oy.2.1 oy.2.2
    (fp_separated state disk x y bytes validX validY different emptyX emptyY)

end MachCSL.Logic.FsDurAlloc
