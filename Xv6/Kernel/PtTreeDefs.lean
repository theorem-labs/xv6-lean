import MachCSL.Machine.RegisterRun
import MachCSL.Machine.PteCanonicalDefs
import MachCSL.Logic.RegisterPlanDefs
import LeanPaperStock.Vmem

/-! Inert page-table descriptions and pure semantic predicates from
`PtreeType.v`, `PtTree.v:90–139,435–579,1862–1868`, paper pin fa7f0a01.
No physical ownership, shared invariant, or successful translation is assumed.
The actual finite register-run witness below concerns the validation function
only; it is not an alternate interpreter for the concurrent machine. -/
namespace Xv6.Kernel.PtTree
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev PPN := BitVec 44
abbrev VPN := BitVec 27
abbrev Index := BitVec 9
abbrev Word := BitVec 64

/-- Exact source carrier: every node has total raw-word and child functions.
There is no validity, allocation geometry, or height restriction in the type. -/
inductive Tree where
  | node (base : PPN) (entries : Index → Word) (children : Index → Option Tree)

def base : Tree → PPN
  | .node b _ _ => b
def entries : Tree → Index → Word
  | .node _ e _ => e
def children : Tree → Index → Option Tree
  | .node _ _ c => c

def validation (w : Word) : SailM Bool :=
  pte_is_invalid (PteCanonical.flags w) (ext_bits_of_PTE w)

/-- Every actual dependent register file has a finite, checked execution
returning this Boolean and the same file. The fuel is existential, not an
assumed fixed budget or an untrusted evaluation result. -/
def Outcome (w : Word) (answer : Bool) : Prop :=
  ∀ rs : RegisterFile, ∃ fuel : Nat,
    registerRun fuel (validation w) rs = some (answer, rs)

def Valid (w : Word) : Prop := Outcome w false
def Invalid (w : Word) : Prop := Outcome w true
def Pointer (w : Word) : Prop := PteCanonical.nonleaf w = true
def Leaf (w : Word) : Prop := PteCanonical.nonleaf w = false
def NoNapot (w : Word) : Prop := _get_PTE_Ext_N (ext_bits_of_PTE w) != 1#1
def PbmtZero (w : Word) : Prop := _get_PTE_Ext_PBMT (ext_bits_of_PTE w) = 0#2

def index : Nat → VPN → Index
  | 2, vpn => vpn.extractLsb 26 18
  | 1, vpn => vpn.extractLsb 17 9
  | _, vpn => vpn.extractLsb 8 0

def nextBase (w : Word) : PPN := PPN_of_PTE (k_pte_size := 64) w
def slotAddress (b : PPN) (i : Index) : Word :=
  (BitVec.append b (BitVec.append i 0#3)).zeroExtend 64
def addr2 (t : Tree) (vpn : VPN) : Word := slotAddress (base t) (index 2 vpn)
def addr1 (p2 : Word) (vpn : VPN) : Word := slotAddress (nextBase p2) (index 1 vpn)
def addr0 (p1 : Word) (vpn : VPN) : Word := slotAddress (nextBase p1) (index 0 vpn)

/-- Source shallow 4-KiB mapping predicate, with arbitrary valid upper words. -/
def Maps (t : Tree) (vpn : VPN) (p2 p1 p0 : Word) : Prop :=
  ∃ c1 c0,
    children t (index 2 vpn) = some c1 ∧
    children c1 (index 1 vpn) = some c0 ∧
    entries t (index 2 vpn) = p2 ∧
    entries c1 (index 1 vpn) = p1 ∧
    entries c0 (index 0 vpn) = p0 ∧
    nextBase p2 = base c1 ∧ nextBase p1 = base c0 ∧
    Valid p2 ∧ Pointer p2 ∧ Valid p1 ∧ Pointer p1 ∧
    Valid p0 ∧ Leaf p0 ∧ NoNapot p0 ∧ PbmtZero p0

/-- Exactly the source's three invalid-stop cases. A valid nonleaf at level
zero is intentionally not added as a fourth case. -/
def Blocks (t : Tree) (vpn : VPN) : Prop :=
  (children t (index 2 vpn) = none ∧ Invalid (entries t (index 2 vpn))) ∨
  (∃ c1,
    children t (index 2 vpn) = some c1 ∧ children c1 (index 1 vpn) = none ∧
    Valid (entries t (index 2 vpn)) ∧ Pointer (entries t (index 2 vpn)) ∧
    nextBase (entries t (index 2 vpn)) = base c1 ∧ Invalid (entries c1 (index 1 vpn))) ∨
  (∃ c1 c0,
    children t (index 2 vpn) = some c1 ∧ children c1 (index 1 vpn) = some c0 ∧
    Valid (entries t (index 2 vpn)) ∧ Pointer (entries t (index 2 vpn)) ∧
    Valid (entries c1 (index 1 vpn)) ∧ Pointer (entries c1 (index 1 vpn)) ∧
    nextBase (entries t (index 2 vpn)) = base c1 ∧
    nextBase (entries c1 (index 1 vpn)) = base c0 ∧ Invalid (entries c0 (index 0 vpn)))

def updateEntry (t : Tree) (i : Index) (w : Word) : Tree :=
  .node (base t) (fun j => if j = i then w else entries t j) (children t)
def updateChild (t : Tree) (i : Index) (c : Option Tree) : Tree :=
  .node (base t) (entries t) (fun j => if j = i then c else children t j)

def setLeaf (t : Tree) (vpn : VPN) (w : Word) : Tree :=
  match children t (index 2 vpn) with
  | none => t
  | some c1 => match children c1 (index 1 vpn) with
    | none => t
    | some c0 => updateChild t (index 2 vpn)
        (some (updateChild c1 (index 1 vpn) (some (updateEntry c0 (index 0 vpn) w))))

/-- Canonicalize just this page, leaving even its inert children untouched. -/
def canonLevel0 (t : Tree) : Tree :=
  .node (base t) (fun i => PteCanonical.canon (entries t i)) (children t)
def canonLevel1 (t : Tree) : Tree :=
  .node (base t) (entries t) (fun i => (children t i).map canonLevel0)
/-- Source fixed three-level canonicalization, not recursion to every leaf. -/
def canon (t : Tree) : Tree :=
  .node (base t) (entries t) (fun i => (children t i).map canonLevel1)

def globalBit (w : Word) : Bool := _get_PTE_Flags_G (PteCanonical.flags w) == 1#1
def globalAfter (initial : Bool) (p2 p1 p0 : Word) : Bool :=
  ((initial || globalBit p2) || globalBit p1) || globalBit p0

end Xv6.Kernel.PtTree
