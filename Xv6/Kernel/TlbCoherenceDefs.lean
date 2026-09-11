import Xv6.Kernel.PtTreeDefs
import Xv6.Kernel.Sv39TlbDefs

/-! Pure single-tree TLB provenance from PtTree.v:1693–1795,1951–1991.
No physical register ownership, shared invariant or hit-translation WP is
asserted by these definitions. -/
namespace Xv6.Kernel.TlbCoherence
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Tlb := Sv39Tlb.Tlb
abbrev Asid := BitVec 16
abbrev index := Sv39Tlb.index

/-- Source stale A/D means any two replacement bits, not a monotone-bit
ordering or equality with current physical memory. -/
def Variant (current cached : PtTree.Word) : Prop :=
  ∃ a d, cached = PteCanonical.setAD current a d

/-- Exact source u_walk_entry at level zero. The origin address comes from
the installing raw level-one PTE, not from a later active root. -/
def entry (asid : Asid) (vpn : PtTree.VPN) (p2 p1 p0 : PtTree.Word) : TLB_Entry :=
  Sv39Tlb.entry asid vpn (PtTree.nextBase p0) p0 (.Physaddr (PtTree.addr0 p1 vpn))
    (PtTree.globalAfter false p2 p1 p0)

/-- The origin VPN can differ from the query while sharing its hash slot. -/
def CacheOf (asid : Asid) (tree : PtTree.Tree) (query : PtTree.VPN) (ent : TLB_Entry) : Prop :=
  ∃ vpn p2 p1 p0 a d,
    PtTree.Maps tree vpn p2 p1 p0 ∧ index vpn = index query ∧
    ent = entry asid vpn p2 p1 (PteCanonical.setAD p0 a d)

/-- Source quantified-through-hash invariant, with checked optional access
rather than an assumed injective hash or an origin=query restriction. -/
def Coherent (asid : Asid) (tree : PtTree.Tree) (tlb : Tlb) : Prop :=
  ∀ query ent, tlb[index query]? = some (some ent) → CacheOf asid tree query ent

def filled (old : Tlb) (asid : Asid) (vpn : PtTree.VPN) (p2 p1 word : PtTree.Word) : Tlb :=
  Sv39Tlb.filled old asid vpn (PtTree.nextBase word) word (.Physaddr (PtTree.addr0 p1 vpn))
    (PtTree.globalAfter false p2 p1 word)

/-- The real hit refresh changes only the stored PTE field in the chosen
entry. PPN, tag, level mask, ASID, global and origin address stay intact. -/
def refreshed (old : Tlb) (idx : Nat) (ent : TLB_Entry) (word : PtTree.Word) : Tlb :=
  _root_.Sail.vectorUpdate old idx (some (tlb_set_pte (k_n := 8) ent word))

/-- Pure residual of the actual one-read lookup, including empty and
foreign-tag cases. The native hash-bound proof rules out invalid indices. -/
def lookupValue (tlb : Tlb) (asid : Asid) (vpn : PtTree.VPN) : Option (Nat × TLB_Entry) :=
  match tlb[index vpn]! with
  | none => none
  | some ent => if match_TLB_Entry ent asid (vpn.signExtend 45) then some (index vpn, ent) else none

def fillAfter (rs : RegisterFile) (asid : Asid) (vpn : PtTree.VPN) (p2 p1 word : PtTree.Word) : RegisterFile :=
  MachCSL.Sail.Registers.write rs .tlb (filled (rs .tlb) asid vpn p2 p1 word)

def refreshAfter (rs : RegisterFile) (idx : Nat) (ent : TLB_Entry) (word : PtTree.Word) : RegisterFile :=
  MachCSL.Sail.Registers.write rs .tlb (refreshed (rs .tlb) idx ent word)

end Xv6.Kernel.TlbCoherence
