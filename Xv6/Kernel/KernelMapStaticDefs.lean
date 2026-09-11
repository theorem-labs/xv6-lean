import Xv6.Kernel.KernelDatumDefs
import MachCSL.Logic.KptGhostDefs

/-! Exact source static identity map from KptPt.v:460–469,795–812.
The large finite map is characterized by lookup; consumers never normalize
its 49,154 entries. This is a ghost-map producer, not a physical table. -/
namespace Xv6.Kernel.KernelMapStatic
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

abbrev VPN := KptGhost.VPN
abbrev PPN := KptGhost.PPN
abbrev Permission := KptGhost.Permission
abbrev Capacity := KernelDatum.Capacity

def identityPPN (vpn : VPN) : PPN := vpn.setWidth 44

def classify (vpn : VPN) : Option Permission :=
  if 0x80000 ≤ vpn.toNat ∧ vpn.toNat < 0x80007 then some .rx
  else if (0x80007 ≤ vpn.toNat ∧ vpn.toNat < 0x88000) ∨
      (0xc000 ≤ vpn.toNat ∧ vpn.toNat < 0x10002) then some .rw
  else none

def Static (vpn : VPN) (permission : Permission) : Prop := classify vpn = some permission

/-- Increasing interval insertions; all keys are unique under the public
range bound. The three disjoint regions have exactly the source lookup. -/
noncomputable def region (lo : Nat) : Nat → Permission → KptGhost.Map
  | 0, _ => ∅
  | n + 1, permission =>
      let vpn := BitVec.ofNat 27 (lo + n)
      (region lo n permission).insert vpn (identityPPN vpn, permission)

@[irreducible] noncomputable def initialMap : KptGhost.Map :=
  ((region 0x80000 7 .rx).union (region 0x80007 0x7ff9 .rw)).union
    (region 0xc000 0x4002 .rw)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

noncomputable def claims (γ : GName) : IProp GF := KptGhost.allClaims capacity.ghost γ initialMap
noncomputable def authority (γ : GName) : IProp GF := KptGhost.mapAuth capacity.ghost γ initialMap

end Xv6.Kernel.KernelMapStatic
