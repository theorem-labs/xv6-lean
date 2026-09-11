import Xv6.Kernel.KptHitDefs
import Xv6.Kernel.KptMissDefs

/-! Actual Sv39 lookup/dispatch over the shared kernel table. This layer
starts at `translate 39`; SATP, translation mode and canonical VA precede it. -/
namespace Xv6.Kernel.KptTranslate
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptShared.Capacity
abbrev Shares := KptMiss.Shares
abbrev Config := KptMiss.Config
abbrev Result := KptMiss.Result
abbrev footprint := KptMiss.footprint

/-- Hit and miss retain different receipt sets and exact event counts. -/
inductive Branch where
  | hit (cachedA cachedD : Bool) (update : KptAD.Branch)
  | miss (cachedA cachedD : Bool) (view2 view1 view0 : Nat) (update : KptAD.Branch)
  deriving DecidableEq

def Branch.cached (ppn : PtTree.PPN) (permission : KptLeaf.Permission) : Branch → PtTree.Word
  | .hit a d _ | .miss a d _ _ _ _ => KptLeaf.word ppn permission a d

def Branch.update : Branch → KptAD.Branch
  | .hit _ _ update | .miss _ _ _ _ _ update => update

def program (asid : BitVec 16) (tree : PtTree.Tree) (vpn : PtTree.VPN)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool) : SailM Result :=
  translate 39 asid (PtTree.base tree) vpn access .Supervisor mxr doSum ()

/-- The actual hit index is retained until coherent lookup proves its value. -/
def dispatch (asid : BitVec 16) (tree : PtTree.Tree) (vpn : PtTree.VPN)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool)
    (found : Option (Nat × TLB_Entry)) : SailM Result :=
  match found with
  | some (idx, ent) => translate_TLB_hit 39 asid vpn access .Supervisor mxr doSum () idx ent
  | none => KptMiss.program asid tree vpn access mxr doSum

def result (ppn : PtTree.PPN) (branch : Branch) : Result :=
  KptMiss.result ppn branch.update

def after (rs : RegisterFile) (asid : BitVec 16) (vpn : PtTree.VPN)
    (p2 p1 : PtTree.Word) (ppn : PtTree.PPN) (permission : KptLeaf.Permission) :
    Branch → RegisterFile
  | .hit a d update => KptHit.after rs vpn
      (TlbCoherence.entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) update
  | .miss a d _ _ _ update => KptMiss.after rs asid vpn p2 p1 ppn
      (KptLeaf.word ppn permission a d) update

/-- Actual lookup selection is a returned fact, not a caller hypothesis. -/
def Selected (rs : RegisterFile) (asid : BitVec 16) (vpn : PtTree.VPN)
    (p2 p1 : PtTree.Word) (ppn : PtTree.PPN) (permission : KptLeaf.Permission) : Branch → Prop
  | .hit a d _ => TlbCoherence.lookupValue (rs .tlb) asid vpn =
      some (TlbCoherence.index vpn,
        TlbCoherence.entry asid vpn p2 p1 (KptLeaf.word ppn permission a d))
  | .miss _ _ _ _ _ _ => TlbCoherence.lookupValue (rs .tlb) asid vpn = none

def BranchFacts (rs : RegisterFile) (asid : BitVec 16) (vpn : PtTree.VPN)
    (p2 p1 : PtTree.Word) (ppn : PtTree.PPN) (permission : KptLeaf.Permission)
    (referenceA referenceD : Bool) (access : MemoryAccessType mem_payload) (branch : Branch) : Prop :=
  Selected rs asid vpn p2 p1 ppn permission branch ∧
    KptAD.BranchFacts (branch.cached ppn permission)
      (KptLeaf.word ppn permission referenceA referenceD) access (KptAD.enabled rs) branch.update

variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev cells := KptMiss.cells capacity

def receipts (era : Era.Record) (cpu : CPU) (address : BitVec 64) : Branch → IProp GF
  | .hit _ _ update => KptAD.receipt capacity era cpu address update
  | .miss _ _ view2 view1 view0 update =>
      iprop(KptTreeWalk.receipts capacity era cpu view2 view1 view0 ∗
        KptAD.receipt capacity era cpu address update)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable abbrev clients := KptMiss.clients capacity

noncomputable def resources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (tree : PtTree.Tree) (bound : Nat)
    (asid : BitVec 16) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word) (ppn : PtTree.PPN)
    (permission : KptLeaf.Permission) (rr : Option Reservation) (branch : Branch) : IProp GF :=
  iprop(cells capacity era cpu (after rs asid vpn p2 p1 ppn permission branch) shares ∗
    clients capacity era cpu N root tree bound ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (KptAD.afterReservation (PtTree.addr0 p1 vpn) rr branch.update) ∗
    receipts capacity era cpu (PtTree.addr0 p1 vpn) branch ∗
    ⌜TlbCoherence.Coherent asid tree (after rs asid vpn p2 p1 ppn permission branch .tlb)⌝)

/-- This is the actual continuation WP after receipt/resource restoration,
not a supplied proof of the translation body. -/
noncomputable def continueWith [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (tree : PtTree.Tree) (bound : Nat)
    (asid : BitVec 16) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word) (ppn : PtTree.PPN)
    (permission : KptLeaf.Permission) (referenceA referenceD : Bool)
    (access : MemoryAccessType mem_payload) (rr : Option Reservation)
    (continuation : Result → SailM Unit) (post : Empty → IProp GF) (branch : Branch) : IProp GF :=
  iprop(⌜BranchFacts rs asid vpn p2 p1 ppn permission referenceA referenceD access branch⌝ -∗
    resources capacity era cpu rs shares N root tree bound asid vpn p2 p1 ppn permission rr branch -∗
    MemoryReadWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (continuation (result ppn branch))) post)

/-- Ordinary conjunction offers the two alternatives without duplicating
resources. The miss's three guards precede its leaf/view selection. All
observed-word and lookup facts remain inside the subsequent A/D guards. -/
noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (tree : PtTree.Tree) (bound : Nat)
    (asid : BitVec 16) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word) (ppn : PtTree.PPN)
    (permission : KptLeaf.Permission) (referenceA referenceD : Bool)
    (access : MemoryAccessType mem_payload) (rr : Option Reservation)
    (continuation : Result → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  let next := continueWith capacity image fixed whole gen era cpu rs shares N root tree bound
    asid vpn p2 p1 ppn permission referenceA referenceD access rr continuation post
  iprop((∀ a d update, KptAD.guarded update (next (.hit a d update))) ∧
    ▷ ▷ ▷ (∀ a d view2 view1 view0 update,
      KptAD.guarded update (next (.miss a d view2 view1 view0 update))))

end Xv6.Kernel.KptTranslate
