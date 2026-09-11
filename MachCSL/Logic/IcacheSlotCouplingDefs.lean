import MachCSL.Logic.IcacheRefLedgerDefs
import MachCSL.Logic.IcacheCouplingDefs
import Xv6.Fs.Dinode

/-! Exact pure and native reference/mirror columns from `InodeRegion.v`.
These are components of `ireg_slot`, not a replacement for its other legs. -/
namespace MachCSL.Logic.IcacheSlotCoupling
open Iris Iris.BI Xv6.Fs IcacheRefLedger

def fresh_shape (d : Dinode) : Prop :=
  d.type.toNat ≠ 0 ∧ d.size.toNat = 0 ∧ d.addrs = List.replicate 13 0 ∧ d.nlink.toNat = 0

def ireg_claim_ok (c : ClaimCell) (f : FreezeCell) (d : Dinode) : Prop :=
  match c with
  | none => True
  | some x => fresh_shape d ∧ f = freezeCell .off ∧
    match x with
    | .excl v => v.car.1 = d.type
    | .invalid => False

def ireg_ref_ok (r rc n : Nat) (c : ClaimCell) (d : Dinode) : Prop :=
  r + rc ≤ n ∧ (d.type.toNat = 0 → r = 0 ∧ rc = 0) ∧ (c ≠ none → r = 0)

def ireg_frzm_ok (b : Bool) (f : FreezeCell) : Prop := b = frz_preb f

def ireg_frz_ok (f : FreezeCell) (n : Nat) (d : Dinode) : Prop :=
  match f with
  | some (.excl phase) => match phase.car with
    | .off => True
    | .pre _ => d.nlink.toNat = 0 ∧ d.type.toNat ≠ 0 ∧ n = 1
    | .post _ => d.nlink.toNat = 0 ∧ d.type.toNat ≠ 0 ∧ n = 0
  | _ => False

variable {GF : BundledGFunctors}

def ireg_rcol (capacity : IcacheRefLedger.Capacity GF) (g : GName)
    (z : Int) (c : ClaimCell) (r : Nat) (f : FreezeCell) (n : Nat) (d : Dinode) : IProp GF :=
  iprop(∃ rc : Nat, link_auth capacity g z c r f rc ∗ ⌜ireg_ref_ok r rc n c d⌝)

def ireg_frzc (capacity : IcacheCoupling.Capacity GF) (names : IcacheCoupling.Names)
    (z : Int) (f : FreezeCell) : IProp GF :=
  iprop(∃ b : Bool, IcacheCoupling.frzm_h capacity names z b ∗ ⌜ireg_frzm_ok b f⌝)

/-- Composition of supplied boot rows. Both count halves, both mirror halves,
and the ledger's held off fragment remain present. No resource is allocated. -/
def bootRows (ledger : IcacheRefLedger.Capacity GF) (coupling : IcacheCoupling.Capacity GF)
    (g : GName) (names : IcacheCoupling.Names) (inums : _root_.Std.ExtTreeSet Int)
    (records : Int → Dinode) : IProp GF :=
  iprop([∗set] z ∈ inums,
    ireg_rcol ledger g z none 0 (freezeCell .off) 0 (records z) ∗
    ifreeze_off ledger g z ∗
    IcacheCoupling.icnt_half coupling names z 0 ∗ IcacheCoupling.icnt_half coupling names z 0 ∗
    ireg_frzc coupling names z (freezeCell .off) ∗ IcacheCoupling.frzm_h coupling names z false)

end MachCSL.Logic.IcacheSlotCoupling
