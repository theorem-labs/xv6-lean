import Xv6.Kernel.KptOwnershipDefs

/-! The source kernel translation tier and virtual context byte. The mapping
claim, positive canonicality, physical RAM address and tier pin are retained
alongside the actual physical byte/timestamp/context resources. -/
namespace Xv6.Kernel.KernelDatum
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KptOwnership.Capacity

inductive Tier where
  | identity | full
  deriving DecidableEq

def Tier.Le : Tier → Tier → Prop
  | .full, .identity => False
  | _, _ => True

def vpn (va : BitVec 64) : PtTree.VPN := va.extractLsb' 12 27

def physical (ppn : PtTree.PPN) (va : BitVec 64) : PhysicalAddress :=
  (BitVec.append ppn (va.extractLsb' 0 12)).zeroExtend 64

def Positive (va : BitVec 64) : Prop := va.toNat < 2^38

def Ram (pa : PhysicalAddress) : Prop := ramLow ≤ pa.toNat ∧ pa.toNat < ramHigh

def Pin : Tier → PtTree.PPN → BitVec 64 → Prop
  | .identity, ppn, va => physical ppn va = va
  | .full, _, _ => True

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

def claim (tier : Tier) (va : BitVec 64) (ppn : PtTree.PPN) : IProp GF :=
  iprop(KptGhost.mapAt capacity.ghost era.kernelMap (vpn va) ppn .rw ∗
    ⌜Positive va ∧ Ram (physical ppn va) ∧ Pin tier ppn va⌝)

def physicalByte (ξ : TsoContext.CtxId) (pa : PhysicalAddress) (dq : DFrac) (byte : Byte) : IProp GF :=
  TsoContext.physPointsto (TsoContextReadWP.contextCapacity capacity.machine)
    (TsoContextReadWP.contextNames era) ξ pa dq byte

def byte (tier : Tier) (ξ : TsoContext.CtxId) (va : BitVec 64)
    (dq : DFrac) (value : Byte) : IProp GF :=
  iprop(∃ ppn, claim capacity era tier va ppn ∗ physicalByte capacity era ξ (physical ppn va) dq value)

/-- Alignment is virtual; each byte retains its own mapping and physical
context resource, including across a page boundary. -/
def word (tier : Tier) (ξ : TsoContext.CtxId) (va : BitVec 64)
    (dq : DFrac) (value : BitVec 64) : IProp GF :=
  iprop(⌜TsoContextWord.Aligned va⌝ ∗ [∗list] j ∈ List.range 8,
    byte capacity era tier ξ (addressAdd va j) dq (nthByte value j))

end Xv6.Kernel.KernelDatum
