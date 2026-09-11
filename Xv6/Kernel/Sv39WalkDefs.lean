import Xv6.Kernel.KptLeafDefs
import MachCSL.Logic.SupervisorPteReadDefs

/-! The actual three-level Sv39 walk through directly owned kernel slots. -/
namespace Xv6.Kernel.Sv39Walk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure Path where
  root : BitVec 44
  table1 : BitVec 44
  table0 : BitVec 44
  leaf : BitVec 44

def pointer (ppn : BitVec 44) : BitVec 64 :=
  (BitVec.append ppn 1#10).zeroExtend 64

def index (vpn : BitVec 27) : Nat → BitVec 9
  | 2 => vpn.extractLsb 26 18
  | 1 => vpn.extractLsb 17 9
  | _ => vpn.extractLsb 8 0

def base (path : Path) : Nat → BitVec 44
  | 2 => path.root
  | 1 => path.table1
  | _ => path.table0

def addressAt (ppn : BitVec 44) (index : BitVec 9) : BitVec 64 :=
  (BitVec.append ppn (BitVec.append index 0#3)).zeroExtend 64

def address (path : Path) (vpn : BitVec 27) (level : Nat) : BitVec 64 :=
  addressAt (base path level) (index vpn level)

def reference (path : Path) (permission : KptLeaf.Permission) : Nat → BitVec 64
  | 2 => pointer path.table1
  | 1 => pointer path.table0
  | _ => KptLeaf.word path.leaf permission false false

abbrev Shares := SupervisorPteRead.Shares
abbrev cells := @SupervisorPteRead.cells
abbrev Result := _root_.Sail.Result (PTW_Output 39 × Unit) (PTW_Error × Unit)

def Config (rs : RegisterFile) (path : Path) (vpn : BitVec 27) (regions : Nat → PMA_Region) : Prop :=
  ∀ level, level < 3 → SupervisorPteRead.Config rs (address path vpn level) (regions level)

def output (path : Path) (vpn : BitVec 27) (permission : KptLeaf.Permission)
    (global a d : Bool) : PTW_Output 39 where
  ppn := path.leaf
  pte := KptLeaf.word path.leaf permission a d
  pteAddr := .Physaddr (address path vpn 0)
  level := 0
  pbmt := .PBMT_PMA
  global := global

def program (path : Path) (vpn : BitVec 27) (access : MemoryAccessType mem_payload)
    (mxr doSum global : Bool) : SailM Result :=
  pt_walk 39 vpn access .Supervisor mxr doSum path.root 2 global ()

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF) (era : Era.Record)

def slot (path : Path) (vpn : BitVec 27) (permission : KptLeaf.Permission)
    (bound : Nat) (dq : Nat → DFrac) (values : Nat → Nat → Byte) (level : Nat) : IProp GF :=
  TsoPinnedReadWP.slot capacity era (address path vpn level) 8 (dq level) (values level)
    bound (PteCanonical.slotSet (reference path permission level))

def slots (path : Path) (vpn : BitVec 27) (permission : KptLeaf.Permission)
    (bound : Nat) (dq : Nat → DFrac) (values : Nat → Nat → Byte) : IProp GF :=
  iprop(slot capacity era path vpn permission bound dq values 2 ∗
    slot capacity era path vpn permission bound dq values 1 ∗
    slot capacity era path vpn permission bound dq values 0)

def receipts (cpu : CPU) (view2 view1 view0 : Nat) : IProp GF :=
  iprop(Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view2 ∗
    Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view1 ∗
    Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view0)

end Xv6.Kernel.Sv39Walk
