import Xv6.Kernel.KptPublishSlotProofs

namespace Xv6.Kernel.KptPublish
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Source's persistent per-child update wand, folded in list order. The
premise is discharged from depth induction, never assumed at the public gate. -/
theorem kids_transform (era : Era.Record) cpu ξ g (P Q : Tree → IProp GF)
    {α : Type} (indices : List α) (children : α → Option Tree) :
    iprop(⊢ (□ ∀ child, heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗ P child ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗ Q child) -∗
      heapAt capacity era g -∗ tsoAt capacity era g -∗ running capacity era cpu ξ -∗
      ([∗list] i ∈ indices, match children i with | none => emp | some child => P child) ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      ([∗list] i ∈ indices, match children i with | none => emp | some child => Q child)) := by
  induction indices with
  | nil =>
    simp only [BigSepL.bigSepL_nil.to_eq]
    iintro #_ Hheap Htso Hrun _
    imodintro
    iframe Hheap Htso Hrun
  | cons i indices ih =>
    rw [BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_cons.to_eq]
    iintro #Hstep Hheap Htso Hrun ⟨Hchild, Hchildren⟩
    cases hc : children i with
    | none =>
      simp only [hc] at *
      imod ih $$ Hstep Hheap Htso Hrun Hchildren with ⟨Hheap, Htso, Hrun, Hchildren⟩
      imodintro
      iframe Hheap Htso Hrun Hchildren
    | some child =>
      simp only [hc] at *
      ihave Hcall := Hstep $$ %child
      imod Hcall $$ Hheap Htso Hrun Hchild with ⟨Hheap, Htso, Hrun, Hchild⟩
      imod ih $$ Hstep Hheap Htso Hrun Hchildren with ⟨Hheap, Htso, Hrun, Hchildren⟩
      imodintro
      iframe Hheap Htso Hrun Hchild Hchildren

theorem tree_view : ∀ era cpu ξ g (depth : Nat) tree,
    ContextPinMint.Drained cpu g →
    iprop(⊢ viewZero capacity era (g.views cpu) -∗
      heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel (g.views cpu)) depth (.own 1) tree) := by
  intro era cpu ξ g depth tree drained
  induction depth generalizing tree with
  | zero =>
    simp only [KptOwnership.treeOwn]
    iintro #Hview Hheap Htso Hrun ⟨Hpage, _⟩
    imod page_view capacity era cpu ξ g tree drained
      $$ Hview Hheap Htso Hrun Hpage with ⟨Hheap, Htso, Hrun, Hpage⟩
    imodintro
    iframe Hheap Htso Hrun Hpage
  | succ depth ih =>
    simp only [KptOwnership.treeOwn]
    iintro #Hview Hheap Htso Hrun ⟨Hpage, Hchildren⟩
    imod page_view capacity era cpu ξ g tree drained
      $$ Hview Hheap Htso Hrun Hpage with ⟨Hheap, Htso, Hrun, Hpage⟩
    ihave #Hstep : (□ ∀ child, heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗ KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) child ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel (g.views cpu)) depth (.own 1) child) $$ []
    · iintro !> %child
      iapply ih child $$ Hview
    imod kids_transform capacity era cpu ξ g
      (KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1))
      (KptOwnership.treeOwn capacity era (.kernel (g.views cpu)) depth (.own 1))
      KptOwnership.indices (PtTree.children tree)
      $$ Hstep Hheap Htso Hrun Hchildren with ⟨Hheap, Htso, Hrun, Hchildren⟩
    imodintro
    iframe Hheap Htso Hrun Hpage Hchildren

theorem tree_boot : ∀ era cpu ξ g (depth : Nat) tree,
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel g.log.length) depth (.own 1) tree) := by
  intro era cpu ξ g depth tree boot
  induction depth generalizing tree with
  | zero =>
    simp only [KptOwnership.treeOwn]
    iintro Hheap Htso Hrun ⟨Hpage, _⟩
    imod page_boot capacity era cpu ξ g tree boot
      $$ Hheap Htso Hrun Hpage with ⟨Hheap, Htso, Hrun, Hpage⟩
    imodintro
    iframe Hheap Htso Hrun Hpage
  | succ depth ih =>
    simp only [KptOwnership.treeOwn]
    iintro Hheap Htso Hrun ⟨Hpage, Hchildren⟩
    imod page_boot capacity era cpu ξ g tree boot
      $$ Hheap Htso Hrun Hpage with ⟨Hheap, Htso, Hrun, Hpage⟩
    ihave #Hstep : (□ ∀ child, heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗ KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) child ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel g.log.length) depth (.own 1) child) $$ []
    · iintro !> %child
      iapply ih child
    imod kids_transform capacity era cpu ξ g
      (KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1))
      (KptOwnership.treeOwn capacity era (.kernel g.log.length) depth (.own 1))
      KptOwnership.indices (PtTree.children tree)
      $$ Hstep Hheap Htso Hrun Hchildren with ⟨Hheap, Htso, Hrun, Hchildren⟩
    imodintro
    iframe Hheap Htso Hrun Hpage Hchildren

end Xv6.Kernel.KptPublish
