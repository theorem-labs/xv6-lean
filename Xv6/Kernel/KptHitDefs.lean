import Xv6.Kernel.KptADDefs
import Xv6.Kernel.Sv39HitDefs
import Xv6.Kernel.Sv39MissDefs

/-! Full shared-kernel hit composition over a resident source entry.
The actual cached entry retains the installing tree's leaf address. -/
namespace Xv6.Kernel.KptHit
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptShared.Capacity
abbrev Shares := KptAD.Shares
abbrev Config := KptAD.Config
abbrev Branch := KptAD.Branch
abbrev Result := Sv39Hit.Result
abbrev footprint := Sv39Miss.footprint
abbrev entry := TlbCoherence.entry

def program (asid : BitVec 16) (vpn : PtTree.VPN) (ent : TLB_Entry)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool) : SailM Result :=
  Sv39Hit.program asid vpn (TlbCoherence.index vpn) ent access mxr doSum

def after (rs : RegisterFile) (vpn : PtTree.VPN) (ent : TLB_Entry) (branch : Branch) : RegisterFile :=
  Sv39Hit.updateAfter rs (TlbCoherence.index vpn) ent (KptAD.result branch)

def result (ppn : PtTree.PPN) : Branch → Result
  | .disabled => .Err (.PTW_PTE_Needs_Update (), ())
  | _ => .Ok (ppn, .PBMT_PMA, ())

variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev cells (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  Sv39Miss.cells capacity.machine era cpu rs shares

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def resources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (asid : BitVec 16) (N : Namespace) (root : PtTree.PPN) (tree : PtTree.Tree)
    (vpn : PtTree.VPN) (ent : TLB_Entry) (address : BitVec 64)
    (rr : Option Reservation) (branch : Branch) : IProp GF :=
  iprop(cells capacity era cpu (after rs vpn ent branch) shares ∗
    KptAD.clients capacity era N root tree ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (KptAD.afterReservation address rr branch) ∗
    KptAD.receipt capacity era cpu address branch ∗
    ⌜TlbCoherence.Coherent asid tree (after rs vpn ent branch .tlb)⌝)

end Xv6.Kernel.KptHit
