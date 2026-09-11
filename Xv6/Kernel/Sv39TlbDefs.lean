import MachCSL.Logic.RegisterPlanDefs
import LeanPaperStock.VmemTlb

namespace Xv6.Kernel.Sv39Tlb
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Tlb := Vector (Option TLB_Entry) 64

def entry (asid : BitVec 16) (vpn : BitVec 27) (ppn : BitVec 44)
    (pte : BitVec 64) (address : physaddr) (global : Bool) : TLB_Entry :=
  ⟨asid, global, vpn.signExtend 45, 0#45, ppn, pte, address⟩

def index (vpn : BitVec 27) : Nat := tlb_hash 39 vpn

def filled (old : Tlb) (asid : BitVec 16) (vpn : BitVec 27) (ppn : BitVec 44)
    (pte : BitVec 64) (address : physaddr) (global : Bool) : Tlb :=
  _root_.Sail.vectorUpdate old (index vpn) (some (entry asid vpn ppn pte address global))

def after (rs : RegisterFile) (asid : BitVec 16) (vpn : BitVec 27) (ppn : BitVec 44)
    (pte : BitVec 64) (address : physaddr) (global : Bool) : RegisterFile :=
  MachCSL.Sail.Registers.write rs .tlb (filled (rs .tlb) asid vpn ppn pte address global)

def footprint : RegisterFootprint.Footprint := [(.tlb, .own 1)]

end Xv6.Kernel.Sv39Tlb
