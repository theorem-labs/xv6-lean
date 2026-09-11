import Xv6.Kernel.KernelMapStaticSpec

namespace Xv6.Kernel.KernelMapStatic
open Iris MachCSL.Machine MachCSL.Logic

theorem region_lookup lo n permission vpn (bound : lo + n ≤ 2^27) :
    (region lo n permission)[vpn]? =
      if lo ≤ vpn.toNat ∧ vpn.toNat < lo + n then some (identityPPN vpn, permission) else none := by
  induction n with
  | zero => simp [region]
  | succ n ih =>
    have small : lo + n < 2^27 := by omega
    have keyNat : (BitVec.ofNat 27 (lo + n)).toNat = lo + n := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    simp only [region, Std.ExtTreeMap.getElem?_insert]
    by_cases same : BitVec.ofNat 27 (lo + n) = vpn
    · subst vpn
      simp [keyNat]
    · have different : vpn.toNat ≠ lo + n := by
        intro equal
        apply same
        apply BitVec.eq_of_toNat_eq
        exact keyNat.trans equal.symm
      simp only [show compare (BitVec.ofNat 27 (lo + n)) vpn ≠ .eq from by
        simpa using same, if_false]
      rw [ih (by omega)]
      have condition : (lo ≤ vpn.toNat ∧ vpn.toNat < lo + n) ↔
          (lo ≤ vpn.toNat ∧ vpn.toNat < lo + (n + 1)) := by omega
      simp only [condition]

private theorem union_lookup (left right : KptGhost.Map) (vpn : VPN) :
    (left.union right)[vpn]? = (right[vpn]?).or (left[vpn]?) := by
  exact Std.ExtTreeMap.getElem?_union

theorem lookup vpn : initialMap[vpn]? =
    (classify vpn).map (fun permission => (identityPPN vpn, permission)) := by
  unfold initialMap
  rw [union_lookup, union_lookup,
    region_lookup _ _ _ _ (by decide), region_lookup _ _ _ _ (by decide),
    region_lookup _ _ _ _ (by decide)]
  unfold classify
  split <;> split <;> split <;> simp_all <;> omega

theorem class_cases vpn permission : Static vpn permission ↔
    (0x80000 ≤ vpn.toNat ∧ vpn.toNat < 0x80007 ∧ permission = .rx) ∨
    (((0x80007 ≤ vpn.toNat ∧ vpn.toNat < 0x88000) ∨
      (0xc000 ≤ vpn.toNat ∧ vpn.toNat < 0x10002)) ∧ permission = .rw) := by
  cases permission <;>
    by_cases text : 0x80000 ≤ vpn.toNat ∧ vpn.toNat < 0x80007 <;>
    by_cases data : (0x80007 ≤ vpn.toNat ∧ vpn.toNat < 0x88000) ∨
      (0xc000 ≤ vpn.toNat ∧ vpn.toNat < 0x10002) <;>
    simp [Static, classify, text, data] <;> omega

theorem bound vpn permission (given : Static vpn permission) : vpn.toNat < 0x88000 := by
  have cases := (class_cases vpn permission).mp given
  omega

theorem identity va (positive : KernelDatum.Positive va) :
    KernelDatum.physical (identityPPN (KernelDatum.vpn va)) va = va := by
  apply BitVec.eq_of_toNat_eq
  change (((identityPPN (KernelDatum.vpn va)) ++ va.extractLsb' 0 12).setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (va.extractLsb' 0 12).isLt]
  simp only [identityPPN, KernelDatum.vpn, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  unfold KernelDatum.Positive at positive
  omega

theorem text_class va (low : 0x80000000 ≤ va.toNat) (high : va.toNat < 0x80007000) :
    Static (KernelDatum.vpn va) .rx := by
  apply (class_cases _ _).mpr
  left
  refine ⟨?_, ?_, rfl⟩ <;>
    simp only [KernelDatum.vpn, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  all_goals omega

theorem data_class va (low : 0x80007000 ≤ va.toNat) (high : va.toNat < 0x88000000) :
    Static (KernelDatum.vpn va) .rw := by
  apply (class_cases _ _).mpr
  right
  refine ⟨Or.inl ⟨?_, ?_⟩, rfl⟩ <;>
    simp only [KernelDatum.vpn, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  all_goals omega

theorem nativePureSpec : PureSpec :=
  ⟨region_lookup, lookup, class_cases, bound, identity, text_class, data_class⟩

end Xv6.Kernel.KernelMapStatic
