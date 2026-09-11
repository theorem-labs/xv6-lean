import Xv6.Kernel.Sv39WalkDefs
import Xv6.Kernel.Sv39TlbDefs
import MachCSL.Logic.SupervisorPteADDefs

namespace Xv6.Kernel.Sv39Miss
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Shares := SupervisorPteAD.Shares
abbrev Branch := SupervisorPteAD.Branch
abbrev Result := _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  SupervisorPteAD.footprint shares ++ [(.tlb, .own 1)]

structure Config (rs : RegisterFile) (path : Sv39Walk.Path) (vpn : BitVec 27)
    (regions : Nat → PMA_Region) : Prop where
  walk : Sv39Walk.Config rs path vpn regions
  update : SupervisorPteAD.Config rs (Sv39Walk.address path vpn 0) (regions 0)

def program (asid : BitVec 16) (path : Sv39Walk.Path) (vpn : BitVec 27)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool) : SailM Result :=
  translate_TLB_miss 39 asid path.root vpn access .Supervisor mxr doSum ()

def result (ppn : BitVec 44) : Branch → Result
  | .disabled => .Err (.PTW_PTE_Needs_Update (), ())
  | _ => .Ok (ppn, .PBMT_PMA, ())

def fillWord (cached physical : BitVec 64) : Branch → BitVec 64
  | .cached => cached
  | .written word => word
  | _ => physical

def after (rs : RegisterFile) (asid : BitVec 16) (path : Sv39Walk.Path) (vpn : BitVec 27)
    (cached physical : BitVec 64) (branch : Branch) : RegisterFile :=
  match branch with
  | .disabled => rs
  | _ => Sv39Tlb.after rs asid vpn path.leaf (fillWord cached physical branch)
      (.Physaddr (Sv39Walk.address path vpn 0)) false

/-- Both successful update responses fill the TLB with their actual word. -/
def afterUpdate (asid : BitVec 16) (vpn : BitVec 27) (walk : PTW_Output 39) :
    SupervisorPteAD.Result → SailM Result
  | .Err error => pure (.Err error)
  | .Ok (word, ext) => do
      add_to_TLB 39 asid vpn walk.ppn (word.getD walk.pte) walk.pteAddr walk.level walk.global
      pure (.Ok (walk.ppn, walk.pbmt, ext))

/-- All walk failures remain before the actual update/fill continuation. -/
def afterWalk (asid : BitVec 16) (vpn : BitVec 27) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) : Sv39Walk.Result → SailM Result
  | .Err error => pure (.Err error)
  | .Ok (walk, ext) =>
      update_and_write_pte 39 vpn walk.pteAddr walk.pte walk.level access .Supervisor mxr doSum ext >>=
        afterUpdate asid vpn walk

def walkDq (dq : Nat → DFrac) (level : Nat) : DFrac := if level = 0 then .own 1 else dq level
def walkValues (values : Nat → Nat → Byte) (physical : BitVec 64) (level : Nat) : Nat → Byte :=
  if level = 0 then nthByte physical else values level

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

def cells (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

/-- The physical leaf can differ in A/D from the ordinary walk's read word. -/
def slots (era : Era.Record) (path : Sv39Walk.Path) (vpn : BitVec 27)
    (permission : KptLeaf.Permission) (physical : BitVec 64) (bound : Nat)
    (dq : Nat → DFrac) (values : Nat → Nat → Byte) : IProp GF :=
  iprop(Sv39Walk.slot capacity era path vpn permission bound dq values 2 ∗
    Sv39Walk.slot capacity era path vpn permission bound dq values 1 ∗
    TsoPinnedReadWP.slot capacity era (Sv39Walk.address path vpn 0) 8 (.own 1)
      (nthByte physical) bound (PteCanonical.slotSet (KptLeaf.word path.leaf permission false false)))

def resources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (asid : BitVec 16) (path : Sv39Walk.Path) (vpn : BitVec 27)
    (permission : KptLeaf.Permission) (cached physical : BitVec 64) (bound : Nat)
    (dq : Nat → DFrac) (values : Nat → Nat → Byte) (rr : Option Reservation)
    (view2 view1 view0 : Nat) (branch : Branch) : IProp GF :=
  iprop(cells capacity era cpu (after rs asid path vpn cached physical branch) shares ∗
    TsoPinnedReadWP.credential capacity era cpu bound ∗
    slots capacity era path vpn permission (SupervisorPteAD.afterWord physical branch) bound dq values ∗
    Reservations.resvFrag capacity.era.reservations era.reservations cpu
      (SupervisorPteAD.afterReservation (Sv39Walk.address path vpn 0) physical rr branch) ∗
    Sv39Walk.receipts capacity era cpu view2 view1 view0 ∗
    SupervisorPteAD.receipt capacity era cpu (Sv39Walk.address path vpn 0) branch ∗
    ⌜PteCanonical.canon (SupervisorPteAD.afterWord physical branch) =
      KptLeaf.word path.leaf permission false false⌝)

end Xv6.Kernel.Sv39Miss
