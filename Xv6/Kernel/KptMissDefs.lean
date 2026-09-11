import Xv6.Kernel.KptTreeWalkDefs
import Xv6.Kernel.KptADDefs
import Xv6.Kernel.TlbCoherenceDefs
import Xv6.Kernel.Sv39MissDefs

/-! Actual shared-kernel TLB miss: no frozen physical leaf word or direct
slot resource is part of this interface. -/
namespace Xv6.Kernel.KptMiss
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptShared.Capacity
abbrev Shares := KptAD.Shares
abbrev Branch := KptAD.Branch
abbrev Result := Sv39Miss.Result
/-- These two reused definitions are the generic raw generated continuations;
none of Sv39Miss's direct-slot or flag-one assumptions is imported into the contract. -/
abbrev afterUpdate := Sv39Miss.afterUpdate
abbrev afterWalk := Sv39Miss.afterWalk

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  KptAD.footprint shares ++ [(.tlb, .own 1)]

structure Config (rs : RegisterFile) (tree : PtTree.Tree) (vpn : PtTree.VPN)
    (p2 p1 : PtTree.Word) (regions : Nat → PMA_Region) : Prop where
  walk : KptTreeWalk.Config rs tree vpn p2 p1 regions
  update : KptAD.Config rs (PtTree.addr0 p1 vpn) (regions 0)

def program (asid : BitVec 16) (tree : PtTree.Tree) (vpn : PtTree.VPN)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool) : SailM Result :=
  translate_TLB_miss 39 asid (PtTree.base tree) vpn access .Supervisor mxr doSum ()

def result (ppn : PtTree.PPN) : Branch → Result
  | .disabled => .Err (.PTW_PTE_Needs_Update (), ())
  | _ => .Ok (ppn, .PBMT_PMA, ())

/-- Selection follows the actual update response: cached on None, observed
on reread, new on write. Disabled never fills; its unused selection is cached. -/
def fillWord (cached : PtTree.Word) : Branch → PtTree.Word
  | .reread observed => observed
  | .written _ new => new
  | _ => cached

/-- The walk's exact raw global accumulation is retained on every fill.
A/D stability later relates this old-word field to the selected fill word. -/
def after (rs : RegisterFile) (asid : BitVec 16) (vpn : PtTree.VPN)
    (p2 p1 : PtTree.Word) (ppn : PtTree.PPN) (cached : PtTree.Word) : Branch → RegisterFile
  | .disabled => rs
  | branch => Sv39Tlb.after rs asid vpn ppn (fillWord cached branch)
      (.Physaddr (PtTree.addr0 p1 vpn)) (PtTree.globalAfter false p2 p1 cached)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def cells (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (footprint shares)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable abbrev clients (era : Era.Record) (cpu : CPU) (N : Namespace)
    (root : PtTree.PPN) (tree : PtTree.Tree) (bound : Nat) : IProp GF :=
  KptTreeWalk.clients capacity era cpu N root tree bound

noncomputable def resources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (tree : PtTree.Tree) (bound : Nat)
    (asid : BitVec 16) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word) (ppn : PtTree.PPN)
    (cached : PtTree.Word) (rr : Option Reservation) (view2 view1 view0 : Nat)
    (branch : Branch) : IProp GF :=
  iprop(cells capacity era cpu (after rs asid vpn p2 p1 ppn cached branch) shares ∗
    clients capacity era cpu N root tree bound ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (KptAD.afterReservation (PtTree.addr0 p1 vpn) rr branch) ∗
    KptTreeWalk.receipts capacity era cpu view2 view1 view0 ∗
    KptAD.receipt capacity era cpu (PtTree.addr0 p1 vpn) branch ∗
    ⌜TlbCoherence.Coherent asid tree (after rs asid vpn p2 p1 ppn cached branch .tlb)⌝)

/-- The three walk guards precede selection of cached A/D and view receipts.
Each branch's own facts are INSIDE its A/D guards: observed words are not
chosen before the actual shared exclusive event. -/
noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (tree : PtTree.Tree) (bound : Nat)
    (asid : BitVec 16) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word) (ppn : PtTree.PPN)
    (permission : KptLeaf.Permission) (referenceA referenceD : Bool)
    (access : MemoryAccessType mem_payload) (rr : Option Reservation)
    (continuation : Result → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  iprop(▷ ▷ ▷ (∀ cachedA cachedD view2 view1 view0 branch,
    KptAD.guarded branch iprop(
      ⌜KptAD.BranchFacts (KptLeaf.word ppn permission cachedA cachedD)
        (KptLeaf.word ppn permission referenceA referenceD) access (KptAD.enabled rs) branch⌝ -∗
      resources capacity era cpu rs shares N root tree bound asid vpn p2 p1 ppn
        (KptLeaf.word ppn permission cachedA cachedD) rr view2 view1 view0 branch -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (continuation (result ppn branch))) post)))

end Xv6.Kernel.KptMiss
