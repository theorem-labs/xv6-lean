import Xv6.Kernel.KernelDatumDefs

/-! Same-page geometry and the native virtual-to-physical context-word
boundary. This is resource access, not a translation execution theorem. -/
namespace Xv6.Kernel.KernelDatumWord
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
open KernelDatum

abbrev Capacity := KernelDatum.Capacity

def claims {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)
    (tier : Tier) (va : BitVec 64) (ppn : PtTree.PPN) : IProp GF :=
  iprop([∗list] j ∈ List.range 8, claim capacity era tier (addressAdd va j) ppn)

end Xv6.Kernel.KernelDatumWord
