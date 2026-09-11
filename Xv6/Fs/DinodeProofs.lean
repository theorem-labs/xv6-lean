import Xv6.Fs.Dinode

/-! Byte-level inversion of the on-disk inode encoder. -/
namespace Xv6.Fs
open MachCSL.Memory

theorem dinodeBytes_addrs (dn : Dinode) (i : Nat) :
    byteAt (dinodeBytes dn) (12 + i) = byteAt (indirectBytes dn.addrs) i := by
  have h := byteAt_append_right
    (halfBytes dn.type ++ halfBytes dn.major ++ halfBytes dn.minor ++ halfBytes dn.nlink ++
      word32Bytes dn.size) (indirectBytes dn.addrs) i
  simpa only [List.length_append, halfBytes, word32Bytes, List.length_cons,
    List.length_nil, Nat.reduceAdd, dinodeBytes, List.append_assoc] using h

theorem decodeDinode_encode (dn : Dinode) (wf : dn.WellFormed) :
    decodeDinode (dinodeBytes dn) = dn := by
  cases dn with
  | mk ty major minor nlink size addrs =>
    change addrs.length = 13 at wf
    unfold decodeDinode
    congr 1
    · apply leAt_word _ _ 2 ty
      intro j hj
      have cases : j = 0 ∨ j = 1 := by omega
      rcases cases with rfl | rfl <;> rfl
    · apply leAt_word _ _ 2 major
      intro j hj
      have cases : j = 0 ∨ j = 1 := by omega
      rcases cases with rfl | rfl <;> rfl
    · apply leAt_word _ _ 2 minor
      intro j hj
      have cases : j = 0 ∨ j = 1 := by omega
      rcases cases with rfl | rfl <;> rfl
    · apply leAt_word _ _ 2 nlink
      intro j hj
      have cases : j = 0 ∨ j = 1 := by omega
      rcases cases with rfl | rfl <;> rfl
    · apply leAt_word _ _ 4 size
      intro j hj
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> rfl
    · apply List.ext_getElem (by simp [wf])
      intro q hq ha
      simp only [List.getElem_map, List.getElem_range]
      apply leAt_word _ _ 4 addrs[q]
      intro j hj
      rw [Nat.add_assoc, dinodeBytes_addrs]
      exact indirectBytes_byte addrs q j ha hj

theorem dinodeBytes_injective (left right : Dinode) (hl : left.WellFormed) (hr : right.WellFormed)
    (same : dinodeBytes left = dinodeBytes right) : left = right := by
  rw [← decodeDinode_encode left hl, ← decodeDinode_encode right hr, same]

end Xv6.Fs
