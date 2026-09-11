import Xv6.Fs.FileBytesDefs
import Xv6.Fs.TreeDiskProofs

namespace Xv6.Fs

theorem takeBlocks_length data (full : ∀ k, (data k).length = 1024) start n :
    (takeBlocks data start n).length = n * 1024 := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [takeBlocks, List.length_append, full, ih]; omega

theorem takeBlocks_lookup data (full : ∀ k, (data k).length = 1024) start n j (bound : j < n * 1024) :
    (takeBlocks data start n)[j]? = some (fileByte data (start * 1024 + j)) := by
  induction n generalizing start j with
  | zero => omega
  | succ n ih =>
    unfold takeBlocks
    by_cases first : j < 1024
    · rw [List.getElem?_append_left (by rw [full]; exact first)]
      unfold fileByte byteAt
      have div : (start * 1024 + j) / 1024 = start := by omega
      have mod : (start * 1024 + j) % 1024 = j := by omega
      rw [div, mod, List.getElem?_eq_getElem (by rw [full]; exact first)]
      rfl
    · rw [List.getElem?_append_right (by rw [full]; omega), full, ih (start + 1) (j - 1024) (by omega)]
      exact congrArg (fun offset => some (fileByte data offset)) (by omega)

theorem fileBytes_takeBlocks data n nb (full : ∀ k, (data k).length = 1024) (bound : n ≤ nb * 1024) :
    fileBytes data n = (takeBlocks data 0 nb).take n := by
  apply List.ext_getElem?
  intro j
  by_cases inside : j < n
  · simp only [fileBytes, List.getElem?_map, List.getElem?_range inside, Option.map_some]
    rw [List.getElem?_take, if_pos inside, takeBlocks_lookup data full 0 nb j (by omega)]
    simp only [Nat.zero_mul, Nat.zero_add]
  · rw [List.getElem?_eq_none_iff.mpr (by rw [fileBytes_length]; omega),
      List.getElem?_eq_none_iff.mpr (by rw [List.length_take]; omega)]

theorem nodeAt_file image sb i (full : BlocksFull image)
    (live : (dinode image sb i).typeZ ≠ 0) (non_directory : (dinode image sb i).typeZ ≠ 1) :
    nodeAt image sb i = some (.file ((takeBlocks (fileData image sb i) 0
      (nblocks (dinode image sb i).sizeZ)).take (dinode image sb i).size.toNat)) := by
  rw [nodeAt_live image sb i live]
  simp only [nodeOf, non_directory, ↓reduceIte]
  congr 2
  apply fileBytes_takeBlocks
  · exact dataOf_sized image _ full
  · unfold nblocks nblk Dinode.sizeZ
    omega

end Xv6.Fs
