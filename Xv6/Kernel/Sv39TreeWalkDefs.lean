import Xv6.Kernel.PtTreeDefs
import Xv6.Kernel.Sv39WalkDefs

/-! Direct native Sv39 walk through source tree paths with arbitrary valid
raw pointer words. Physical slots remain directly owned; this is not shared
KPT invariant access or TLB coherence. -/
namespace Xv6.Kernel.Sv39TreeWalk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Shares := SupervisorPteRead.Shares
abbrev cells := @SupervisorPteRead.cells
abbrev Result := Sv39Walk.Result

/-- This record supplies geometry only. Its flag-one reference function is
never used for either raw upper slot. -/
def geometry (tree : PtTree.Tree) (p2 p1 : PtTree.Word) (ppn : PtTree.PPN) : Sv39Walk.Path :=
  ⟨PtTree.base tree, PtTree.nextBase p2, PtTree.nextBase p1, ppn⟩

/-- All three addresses use the source 64-bit raw PTE's 44-bit PPN field.
G/RSW bits are never replaced by a flag-one representative. -/
def address (tree : PtTree.Tree) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word) : Nat → BitVec 64
  | 2 => PtTree.addr2 tree vpn
  | 1 => PtTree.addr1 p2 vpn
  | _ => PtTree.addr0 p1 vpn

/-- Canonical leaf reference is independent of both the tree's A/D pair
and the current physical bytes. Upper references are the entire raw words. -/
def reference (p2 p1 : PtTree.Word) (ppn : PtTree.PPN) (permission : KptLeaf.Permission) :
    Nat → PtTree.Word
  | 2 => p2
  | 1 => p1
  | _ => KptLeaf.word ppn permission false false

def Config (rs : RegisterFile) (tree : PtTree.Tree) (vpn : PtTree.VPN)
    (p2 p1 : PtTree.Word) (regions : Nat → PMA_Region) : Prop :=
  ∀ level, level < 3 → SupervisorPteRead.Config rs (address tree vpn p2 p1 level) (regions level)

/-- The actual generated program begins at the tree root. It neither reads
nor executes the pure child-description functions. Maps supplies that tie. -/
def program (tree : PtTree.Tree) (vpn : PtTree.VPN) (access : MemoryAccessType mem_payload)
    (mxr doSum global : Bool) : SailM Result :=
  pt_walk 39 vpn access .Supervisor mxr doSum (PtTree.base tree) 2 global ()

def output (vpn : PtTree.VPN) (p2 p1 : PtTree.Word) (ppn : PtTree.PPN)
    (permission : KptLeaf.Permission) (global a d : Bool) : PTW_Output 39 where
  ppn := ppn
  pte := KptLeaf.word ppn permission a d
  pteAddr := .Physaddr (PtTree.addr0 p1 vpn)
  level := 0
  pbmt := .PBMT_PMA
  global := PtTree.globalAfter global p2 p1 (KptLeaf.word ppn permission a d)

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF) (era : Era.Record)

def slot (tree : PtTree.Tree) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word)
    (ppn : PtTree.PPN) (permission : KptLeaf.Permission)
    (bound : Nat) (dq : Nat → DFrac) (values : Nat → Nat → Byte) (level : Nat) : IProp GF :=
  TsoPinnedReadWP.slot capacity era (address tree vpn p2 p1 level) 8 (dq level) (values level)
    bound (PteCanonical.slotSet (reference p2 p1 ppn permission level))

def slots (tree : PtTree.Tree) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word)
    (ppn : PtTree.PPN) (permission : KptLeaf.Permission)
    (bound : Nat) (dq : Nat → DFrac) (values : Nat → Nat → Byte) : IProp GF :=
  iprop(slot capacity era tree vpn p2 p1 ppn permission bound dq values 2 ∗
    slot capacity era tree vpn p2 p1 ppn permission bound dq values 1 ∗
    slot capacity era tree vpn p2 p1 ppn permission bound dq values 0)

abbrev receipts := @Sv39Walk.receipts

end Xv6.Kernel.Sv39TreeWalk
