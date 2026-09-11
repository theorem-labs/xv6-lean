import MachCSL.Logic.IcacheTopRegistrySpec

namespace MachCSL.Logic.IcacheTopRegistry
open Iris Iris.Std

theorem clean_empty (nodes : Xv6.Fs.DurableState.InodeMap)
    (localNodes : ∀ i node, nodes[i]? = some node → Xv6.Fs.DurableNode.Local i node) : clean nodes ∅ :=
  fun i node found _ => localNodes i node found

theorem clean_empty_local (nodes : Xv6.Fs.DurableState.InodeMap) (h : clean nodes ∅) :
    ∀ i node, nodes[i]? = some node → Xv6.Fs.DurableNode.Local i node := by
  intro i node found
  apply h i node found
  intro k t q S member
  simp only [get?_empty, reduceCtorEq] at member

theorem clean_insert (nodes : Xv6.Fs.DurableState.InodeMap) (arms : ArmMap Entry)
    (k : Nat) (entry : Entry) (fresh : get? arms k = none) (h : clean nodes arms) :
    clean nodes (PartialMap.insert arms k entry) := by
  intro i node found clear
  apply h i node found
  intro j t q S member
  have ne : k ≠ j := by intro eq; subst j; simp [fresh] at member
  exact clear j t q S (by rw [get?_insert_ne ne]; exact member)

theorem clean_disarm (nodes : Xv6.Fs.DurableState.InodeMap) (arms : ArmMap Entry)
    (k t : Nat) (q : Qp) (S : InumSet) (i : Int) (node : FsTop.Node)
    (entry : get? arms k = some ((t,q),S)) (nodeAt : nodes[i]? = some node)
    (nodeLocal : Xv6.Fs.DurableNode.Local i node) (h : clean nodes arms) :
    clean nodes (PartialMap.insert arms k ((t,q),S \ {i})) := by
  intro j other found clear
  by_cases same : j = i
  · subst j
    have eq : other = node := Option.some.inj (found.symm.trans nodeAt)
    simpa [eq] using nodeLocal
  · apply h j other found
    intro l u r T member
    by_cases key : k = l
    · subst l
      have eq : ((t,q),S) = ((u,r),T) := Option.some.inj (entry.symm.trans member)
      cases eq
      have outside := clear k t q (S \ {i}) (get?_insert_eq rfl)
      intro inside
      apply outside
      simpa only [LawfulSet.mem_diff, LawfulSet.mem_singleton] using And.intro inside same
    · exact clear l u r T (by rw [get?_insert_ne key]; exact member)

theorem clean_release (nodes : Xv6.Fs.DurableState.InodeMap) (arms : ArmMap Entry)
    (k t : Nat) (q : Qp) (entry : get? arms k = some ((t,q),∅)) (h : clean nodes arms) :
    clean nodes (PartialMap.delete arms k) := by
  intro i node found clear
  apply h i node found
  intro l u r S member
  by_cases key : k = l
  · subst l
    have eq : ((t,q),(∅ : InumSet)) = ((u,r),S) := Option.some.inj (entry.symm.trans member)
    cases eq
    simp
  · exact clear l u r S (by rw [get?_delete_ne key]; exact member)

end MachCSL.Logic.IcacheTopRegistry
