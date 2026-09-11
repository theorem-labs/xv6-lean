import Xv6.Fs.DurableImageNodeDefs
import Xv6.Fs.DurableNodeProofs
import Xv6.Fs.BootImageProofs

namespace Xv6.Fs.DurableImageNode
open DurableNode

private theorem leAt32_bound (bytes : List (BitVec 8)) (offset : Nat) :
    0 ≤ leAt bytes offset 4 ∧ leAt bytes offset 4 < 2 ^ 32 := by
  have h := MachCSL.Memory.assembleBytes_bound
    ((List.range 4).map fun j => byteAt bytes (offset + j))
  simp only [List.length_map, List.length_range] at h
  unfold leAt
  constructor <;> omega

private theorem entries_bound (image : Blocks) (dn : Dinode) (i : Nat) :
    0 ≤ (indirectEntries image dn)[i]?.getD 0 ∧
      (indirectEntries image dn)[i]?.getD 0 < 2 ^ 32 := by
  unfold indirectEntries
  dsimp only
  split
  · simp only [List.getElem?_replicate]
    split <;> decide
  · rw [List.getElem?_map]
    cases he : (List.range 256)[i]? with
    | none => change 0 ≤ (0 : Int) ∧ (0 : Int) < 2 ^ 32; decide
    | some j => exact leAt32_bound _ _

private theorem cast32 (z : Int) (h : 0 ≤ z ∧ z < 2 ^ 32) :
    ((BitVec.ofInt 32 z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt]
  change ((z % (2 ^ 32 : Int)).toNat : Int) = z
  rw [Int.emod_eq_of_lt h.1 h.2, Int.toNat_of_nonneg h.1]

private theorem entries_cast (image : Blocks) (dn : Dinode) (i : Nat) :
    (((indirectEntries image dn).map (BitVec.ofInt 32))[i]?.getD 0).toNat =
      ((indirectEntries image dn)[i]?.getD 0).toNat := by
  rw [List.getElem?_map]
  have bound := entries_bound image dn i
  cases he : (indirectEntries image dn)[i]? with
  | none => rfl
  | some z =>
    have hz : 0 ≤ z ∧ z < 2 ^ 32 := by simpa only [he, Option.getD_some] using bound
    change (BitVec.ofInt 32 z).toNat = z.toNat
    have hc := congrArg Int.toNat (cast32 z hz)
    simpa only [Int.toNat_natCast] using hc

theorem imageNode_record (image : Blocks) (sb : Superblock) (i : Int) :
    (imageNode image sb i).record = dinode image sb i := rfl

theorem imageNode_entries (image : Blocks) (sb : Superblock) (i : Int) :
    (imageNode image sb i).entries = (indirectEntries image (dinode image sb i)).map (BitVec.ofInt 32) := rfl

theorem imageNode_address (image : Blocks) (sb : Superblock) (i : Int) (k : Nat) :
    (imageNode image sb i).address k = blockAddress image (dinode image sb i) k := by
  unfold Node.address blockAddress
  by_cases hk : k < 12
  · simp only [hk, if_true, imageNode_record, Dinode.addrZ]
  · simp only [hk, if_false, imageNode_entries, entries_cast]
    exact Int.toNat_of_nonneg (entries_bound image (dinode image sb i) (k - 12)).1

theorem imageNode_indirect (image : Blocks) (sb : Superblock) (i : Int) :
    (imageNode image sb i).indirect = (dinode image sb i).addrZ 12 := rfl

theorem imageNode_lookup (image : Blocks) (sb : Superblock) (i : Int) (k : Nat) :
    (imageNode image sb i).blocks[k]? =
      if k < 268 ∧ blockAddress image (dinode image sb i) k ≠ 0
      then some (dataOf image (dinode image sb i) k) else none := by
  unfold imageNode
  rw [nodeOf_lookup]
  change (if k < 268 ∧ (imageNode image sb i).address k ≠ 0 then _ else _) = _
  rw [imageNode_address]

theorem imageNode_repr (image : Blocks) (sb : Superblock) (i : Int) : Repr (imageNode image sb i) where
  record := dinode_wf image sb i
  entryLength := by rw [imageNode_entries, List.length_map, indirectEntries_length]
  indirectZero := by
    intro hz
    rw [imageNode_entries]
    unfold indirectEntries
    change (dinode image sb i).addrZ 12 = 0 at hz
    simp only [Dinode.addrZ] at hz
    simp only [hz, BEq.rfl, ↓reduceIte, List.map_replicate]
    rfl
  domain := by
    intro k hk
    rw [imageNode_lookup, imageNode_address]
    by_cases hz : blockAddress image (dinode image sb i) k = 0 <;> simp [hk, hz]
  top := by intro k hk; rw [imageNode_lookup, if_neg (by omega)]

theorem imageNode_data (image : Blocks) (sb : Superblock) (i : Int) (k : Nat) (hk : k < 268) :
    (imageNode image sb i).data k = dataOf image (dinode image sb i) k := by
  unfold Node.data
  rw [imageNode_lookup]
  by_cases hz : blockAddress image (dinode image sb i) k = 0
  · rw [if_neg (by simp [hz]), Option.getD_none, dataOf_holes image _ k hz]
  · rw [if_pos ⟨hk,hz⟩, Option.getD_some]

theorem nodesUpto_lookup (image : Blocks) (sb : Superblock) (count : Nat) (i : Int) :
    (nodesUpto image sb count)[i]? =
      if 0 ≤ i ∧ i < (count : Int) then some (imageNode image sb i) else none := by
  induction count with
  | zero => simp only [nodesUpto, Std.ExtTreeMap.getElem?_empty]; rw [if_neg (by omega)]
  | succ count ih =>
    rw [nodesUpto, Std.ExtTreeMap.getElem?_insert]
    simp only [Std.compare_eq_eq_iff_eq]
    by_cases he : (count : Int) = i
    · subst i; rw [if_pos rfl, if_pos (by omega)]
    · rw [if_neg he, ih]
      have hc : (0 ≤ i ∧ i < (count : Int)) ↔ (0 ≤ i ∧ i < ((count + 1 : Nat) : Int)) := by omega
      simp only [hc]

theorem imageNodes_lookup (image : Blocks) (sb : Superblock) (nib : Nat) (i : Int) :
    (imageNodes image sb nib)[i]? =
      if 0 ≤ i ∧ i < 16 * (nib : Int) then some (imageNode image sb i) else none := by
  rw [imageNodes, nodesUpto_lookup]
  simp only [Int.natCast_mul, Int.cast_ofNat_Int]
  rfl

theorem imageNodes_lookup_inv (image : Blocks) (sb : Superblock) (nib : Nat) (i : Int)
    (n : Node) (h : (imageNodes image sb nib)[i]? = some n) :
    (0 ≤ i ∧ i < 16 * (nib : Int)) ∧ n = imageNode image sb i := by
  rw [imageNodes_lookup] at h
  split at h
  · exact ⟨‹_›, (Option.some.inj h).symm⟩
  · contradiction

theorem imageNode_data_all (image : Blocks) (sb : Superblock) (i : Int) :
    (imageNode image sb i).data = dataOf image (dinode image sb i) := by
  funext k
  by_cases hk : k < 268
  · exact imageNode_data image sb i k hk
  · have hz : blockAddress image (dinode image sb i) k = 0 := by
      unfold blockAddress
      rw [if_neg (by omega), List.getElem?_eq_none (by rw [indirectEntries_length]; omega)]
      rfl
    rw [dataOf_holes image _ k hz]
    apply data_missing
    rw [imageNode_lookup, if_neg (by omega)]

theorem imageNode_bare (image : Blocks) (sb : Superblock) (nib : Nat) (i : Int)
    (bare : regionBare image sb nib = true) (nlink : regionNlink image sb nib = true)
    (bound : 0 ≤ i ∧ i < 16 * (nib : Int)) (free : (dinode image sb i).typeZ = 0) :
    (imageNode image sb i).Bare := by
  have addr (k : Nat) := regionBare_addr image sb nib i k bare bound free
  have addrs : (dinode image sb i).addrs = List.replicate 13 0 := by
    apply List.ext_getElem
    · exact (dinode_wf image sb i).trans (List.length_replicate ..).symm
    · intro k hk hk'
      rw [List.getElem_replicate]
      apply BitVec.eq_of_toNat_eq
      have ha := addr k
      simp only [Dinode.addrZ, List.getElem?_eq_getElem hk, Option.getD_some] at ha
      exact_mod_cast ha
  have entries := (imageNode_repr image sb i).indirectZero (addr 12)
  refine ⟨addrs, entries, ?_, regionBare_size image sb nib i bare bound free, ?_⟩
  · apply Std.ExtTreeMap.ext_getElem?
    intro k
    rw [imageNode_lookup, Std.ExtTreeMap.getElem?_empty]
    have hz : blockAddress image (dinode image sb i) k = 0 := by
      rw [← imageNode_address]
      unfold Node.address
      rw [imageNode_record]
      split
      · exact addr k
      · rw [entries, List.getElem?_replicate]
        split <;> rfl
    rw [if_neg (by simp [hz])]
  · have hz := regionNlink_free image sb nib i nlink bound free
    change (dinode image sb i).nlink.toNat = 0
    unfold Dinode.nlinkZ at hz
    omega

theorem imageNode_local_free (image : Blocks) (sb : Superblock) (nib : Nat) (i : Int)
    (bare : regionBare image sb nib = true) (nlink : regionNlink image sb nib = true)
    (bound : 0 ≤ i ∧ i < 16 * (nib : Int)) (free : (dinode image sb i).typeZ = 0) :
    DurableNode.Local i (imageNode image sb i) :=
  local_bare (imageNode_bare image sb nib i bare nlink bound free) (Or.inl free)

theorem imageNode_local_live (h : BootImageWF disk ndisk sb nib cov) (i : Int)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (live : (dinode (blocks disk) sb i).typeZ ≠ 0) :
    DurableNode.Local i (imageNode (blocks disk) sb i) := by
  have repr := imageNode_repr (blocks disk) sb i
  have checks := (fsimgValid_iff (blocks disk) sb).mp h.image
  have ok := inodesValid_spec (blocks disk) sb i checks.inodes bound live
  have region : 0 ≤ i ∧ i < 16 * (nib : Int) := ⟨bound.1, by have := h.advertised; omega⟩
  have dir (hd : (imageNode (blocks disk) sb i).isDir = true) :
      DirectoryOK (blocks disk) sb i (dinode (blocks disk) sb i) := by
    apply dirsValid_spec (blocks disk) sb checks.directories i bound
    simpa only [Node.isDir, Node.typeZ, imageNode_record, beq_iff_eq] using hd
  refine ⟨repr.record, repr.entryLength, repr.indirectZero, repr.domain, repr.top,
    ?_, Or.inr ok.type, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k bytes lookup
    rw [imageNode_lookup] at lookup
    split at lookup
    · cases Option.some.inj lookup
      exact dataOf_sized (blocks disk) _ (blocks_length disk) k
    · contradiction
  · exact ⟨by unfold Node.sizeZ Dinode.sizeZ; omega, ok.size⟩
  · intro k hk hsize
    rw [imageNode_address]
    have haddr := InodeOK.block (blocks disk) sb _ ok k hk hsize
    have hmeta := superblock_metadata sb (bootImage_superblock h)
    omega
  · intro free; exact False.elim (live free)
  · exact regionNlink_short (blocks disk) sb nib i
      (regionValid_nlink _ _ _ h.region) region
  · intro hd; exact (dir hd).gran
  · intro hd
    rw [imageNode_data_all]
    exact (dir hd).unique
  · intro hd hn
    rw [Node.dirEntries, if_pos hd, imageNode_data_all]
    exact (dir hd).dot
  · intro hd hn
    rw [Node.dirEntries, if_pos hd, imageNode_data_all]
    obtain ⟨value, lookup⟩ := (dir hd).dotdot
    change (dirView (dataOf (blocks disk) (dinode (blocks disk) sb i))
      (dirNrec (dinode (blocks disk) sb i).sizeZ))[dotdotName]?.isSome
    rw [lookup]
    rfl
  · intro free; exact False.elim (live free)

theorem imageNode_local (h : BootImageWF disk ndisk sb nib cov) (i : Int)
    (bound : 0 ≤ i ∧ i < 16 * (nib : Int)) :
    DurableNode.Local i (imageNode (blocks disk) sb i) := by
  by_cases free : (dinode (blocks disk) sb i).typeZ = 0
  · exact imageNode_local_free (blocks disk) sb nib i h.bare
      (regionValid_nlink _ _ _ h.region) bound free
  · have inside : i < sb.ninodes := by
      by_cases hi : i < sb.ninodes
      · exact hi
      · have := regionFree_spec (blocks disk) sb nib i
          (regionValid_free _ _ _ h.region) bound.1 (by omega) bound.2
        exact False.elim (free this)
    exact imageNode_local_live h i ⟨bound.1, inside⟩ free

theorem imageNode_dirLocal (h : BootImageWF disk ndisk sb nib cov) (i : Int)
    (bound : 0 ≤ i ∧ i < 16 * (nib : Int)) :
    DurableNode.DirLocal i nib (imageNode (blocks disk) sb i) := by
  by_cases directory : (dinode (blocks disk) sb i).typeZ = 1
  · have inside : 0 ≤ i ∧ i < sb.ninodes := by
      refine ⟨bound.1, ?_⟩
      by_cases hi : i < sb.ninodes
      · exact hi
      · have := regionFree_spec (blocks disk) sb nib i
          (regionValid_free _ _ _ h.region) bound.1 (by omega) bound.2
        omega
    have checks := (fsimgValid_iff (blocks disk) sb).mp h.image
    have dir := dirsValid_spec (blocks disk) sb checks.directories i inside directory
    refine ⟨?_, ?_, ?_⟩
    · intro ht
      rw [imageNode_data_all]
      exact directory_ok_inums _ _ _ _ nib dir h.advertised
    · rw [imageNode_record, imageNode_data_all]
      exact dotsAll_spec _ _ checks.dots i inside directory
    · intro ht hn
      have ok := inodesValid_spec (blocks disk) sb i checks.inodes inside (by omega)
      change (dinode (blocks disk) sb i).nlink.toNat = 0 at hn
      have hnpos := ok.nlink
      unfold Dinode.nlinkZ at hnpos
      omega
  · exact dirLocal_not_dir _ i nib directory

/-- Source list_to_map lookup is independent of enumeration order because
all occurrences of a key carry that key's same decoded node. -/
theorem nodesFromKeys_lookup (image : Blocks) (sb : Superblock) (keys : List Int) (i : Int) :
    (keys.foldr (fun k acc => acc.insert k (imageNode image sb k))
      (∅ : DurableState.InodeMap))[i]? =
      if i ∈ keys then some (imageNode image sb i) else none := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    rw [List.foldr_cons, Std.ExtTreeMap.getElem?_insert]
    simp only [Std.compare_eq_eq_iff_eq, List.mem_cons]
    by_cases equal : key = i
    · subst key; simp
    · rw [if_neg equal, ih]
      simp only [show i ≠ key from Ne.symm equal, false_or]

theorem imageNodes_source_map (image : Blocks) (sb : Superblock) (nib : Nat)
    (keys : List Int) (domain : ∀ i : Int, i ∈ keys ↔ 0 ≤ i ∧ i < 16 * (nib : Int)) :
    imageNodes image sb nib = keys.foldr
      (fun k acc => acc.insert k (imageNode image sb k)) (∅ : DurableState.InodeMap) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro i
  rw [imageNodes_lookup, nodesFromKeys_lookup]
  simp only [domain]

/-- Free inode values remain present; this is not the live-only tree map. -/
theorem imageNodes_keeps_free (image : Blocks) (sb : Superblock) (nib : Nat) (i : Int)
    (bound : 0 ≤ i ∧ i < 16 * (nib : Int)) :
    (imageNodes image sb nib)[i]? = some (imageNode image sb i) := by
  rw [imageNodes_lookup, if_pos bound]

end Xv6.Fs.DurableImageNode
