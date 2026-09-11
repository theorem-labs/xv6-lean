import Xv6.Kernel.PtTreeDefs
import Xv6.Generated.KernelMapsMetadata
import MachCSL.Logic.KptGhostDefs
import MachCSL.Logic.TsoPinnedReadWPDefs
import MachCSL.Logic.TsoContextReadWPDefs

/-! Source `PtTree.v` tiered ownership and `PageGeom.v` geometry.
The inert description has no built-in page separation or memory validity.
All physical resources reside in these native Iris assertions. -/
namespace Xv6.Kernel.KptOwnership
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Tree := PtTree.Tree
abbrev PPN := PtTree.PPN
abbrev VPN := PtTree.VPN
abbrev Index := PtTree.Index
abbrev Word := PtTree.Word

/-- A single machine supplies every byte, timestamp, context and view camera.
The ghost adapter below cannot select an independent view or log capacity. -/
structure Capacity (GF : BundledGFunctors) where
  machine : MachineInterp.Capacity GF
  mapping : GhostMapG GF KptGhost.VPN KptGhost.Mapping KptGhost.KeyMap
  tree : ElemG GF KptGhost.TreeRF
  bound : ElemG GF KptGhost.BoundRF

@[reducible] def Capacity.ghost {GF : BundledGFunctors} (c : Capacity GF) : KptGhost.Capacity GF :=
  ⟨c.mapping, c.tree, c.bound, c.machine.era.views⟩

inductive Tier where
  | kernel (bound : Nat)
  | user (context : TsoContext.CtxId)
  deriving DecidableEq

/-- Exact source page lower bound, tied to the imported image symbol. -/
def kmemLow : Int := Xv6.Generated.KernelMaps.Symbols.end_
def kmemHigh : Int := 0x88000000
def pageSize : Nat := 4096

def pageBase (b : PPN) : PhysicalAddress := (BitVec.append b 0#12).zeroExtend 64
def pageVpn (b : PPN) : VPN := (PtTree.slotAddress b 0#9).extractLsb 38 12

def PageValid (p : PhysicalAddress) : Prop :=
  p.toNat % pageSize = 0 ∧ kmemLow ≤ (p.toNat : Int) ∧ (p.toNat : Int) < kmemHigh

/-- Whole-page RAM coverage, not merely membership of its first address. -/
def NodeData (b : PPN) : Prop :=
  0x80000000 ≤ b.toNat * 4096 ∧ b.toNat * 4096 + 4096 ≤ 0x88000000

/-- The source's ascending seqZ 0 512, represented after its checked word
conversion. Each of the 512 possible indices occurs exactly once. -/
def indices : List Index := (List.range 512).map (BitVec.ofNat 9)

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

def kernelSlot (B : Nat) (a : PhysicalAddress) (dq : DFrac) (word : Word) : IProp GF :=
  iprop(⌜is_aligned_paddr (.Physaddr a) 8 = true⌝ ∗
    TsoPinnedReadWP.slot capacity.machine era a 8 dq (nthByte word) B (PteCanonical.slotSet word))

def slotOwn (tier : Tier) (a : PhysicalAddress) (dq : DFrac) (word : Word) : IProp GF :=
  match tier with
  | .kernel B => kernelSlot capacity era B a dq word
  | .user ξ => TsoContextReadWP.wordPointsto capacity.machine era ξ a dq word

/-- The raw physical-word assertion obtained by forgetting either tier's
extra ghost obligations. It retains actual alignment and all eight bytes. -/
def rawWord (a : PhysicalAddress) (dq : DFrac) (word : Word) : IProp GF :=
  iprop(⌜is_aligned_paddr (.Physaddr a) 8 = true⌝ ∗
    [∗list] j ∈ List.range 8,
      Tso.physBytePointsto capacity.machine.era.heap.ledger era.heap (addressAdd a j) dq (nthByte word j))

/-- The persistent source claim: RAM coverage, kalloc geometry and an identity
RW mapping. No map-ghost assertion implies the other two conjuncts. -/
def nodeClaim (b : PPN) : IProp GF :=
  iprop(⌜NodeData b⌝ ∗ ⌜PageValid (pageBase b)⌝ ∗
    KptGhost.mapAt capacity.ghost era.kernelMap (pageVpn b) b .rw)

def pageOwn (tier : Tier) (dq : DFrac) (t : Tree) : IProp GF :=
  iprop(nodeClaim capacity era (PtTree.base t) ∗
    [∗list] i ∈ indices,
      slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) i) dq (PtTree.entries t i))

/-- Recursion is on the explicit depth, not the inert tree. At depth zero
children remain in the description but contribute no child ownership. -/
noncomputable def treeOwn (tier : Tier) : Nat → DFrac → Tree → IProp GF
  | 0, dq, t => iprop(pageOwn capacity era tier dq t ∗ emp)
  | depth + 1, dq, t => iprop(pageOwn capacity era tier dq t ∗
      [∗list] i ∈ indices, match PtTree.children t i with
        | none => emp
        | some child => treeOwn tier depth dq child)

noncomputable def kidsOwn (tier : Tier) (depth : Nat) (dq : DFrac) (t : Tree) : IProp GF :=
  iprop([∗list] i ∈ indices, match PtTree.children t i with
    | none => emp
    | some child => treeOwn capacity era tier depth dq child)

end Xv6.Kernel.KptOwnership
