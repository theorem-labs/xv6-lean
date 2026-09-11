import Xv6.Kernel.KernelDatumDefs
import MachCSL.Logic.TsoContextBytesReadWPDefs

/-! Same-page geometry and the native virtual-to-physical context-word
boundary for the four-byte noff/intena fields. This is resource access,
not a translation or instruction execution theorem. -/
namespace Xv6.Kernel.KernelDatumWord4
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
open KernelDatum

abbrev Capacity := KernelDatum.Capacity

def Aligned (va : BitVec 64) : Prop := va.toNat % 4 = 0

/-- Four actual source bytes at their original translation tier. -/
def word {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)
    (tier : Tier) (ξ : TsoContext.CtxId) (va : BitVec 64) (dq : DFrac)
    (value : BitVec 32) : IProp GF :=
  iprop(⌜Aligned va⌝ ∗ [∗list] j ∈ List.range 4,
    KernelDatum.byte capacity era tier ξ (addressAdd va j) dq (nthByte value j))

/-- The corresponding physical context window, with actual alignment. -/
def physicalWord {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)
    (ξ : TsoContext.CtxId) (pa : PhysicalAddress) (dq : DFrac) (value : BitVec 32) : IProp GF :=
  iprop(⌜Aligned pa⌝ ∗ TsoContextBytesReadWP.window capacity.machine era ξ pa 4 dq value)

def claims {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)
    (tier : Tier) (va : BitVec 64) (ppn : PtTree.PPN) : IProp GF :=
  iprop([∗list] j ∈ List.range 4, claim capacity era tier (addressAdd va j) ppn)

end Xv6.Kernel.KernelDatumWord4
