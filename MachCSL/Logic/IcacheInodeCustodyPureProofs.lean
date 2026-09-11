import MachCSL.Logic.IcacheInodeCustodyDefs

namespace MachCSL.Logic.IcacheInodeCustody
open Xv6.Fs

theorem freeNode_record (d : Dinode) : (freeNode d).record = d := rfl

theorem freeNode_of_bare (n : DurableNode.Node) (h : n.Bare) : n = freeNode n.record := by
  cases n with
  | mk record entries blocks =>
    rcases h with ⟨_, he, hb, _, _⟩
    change entries = List.replicate 256 0 at he
    change blocks = ∅ at hb
    subst entries
    subst blocks
    rfl

theorem freeNode_bare (d : Dinode) (hb : ireg_bare d) (hn : d.nlinkZ = 0) :
    (freeNode d).Bare := by
  rcases hb with ⟨hs, ha⟩
  refine ⟨ha, rfl, rfl, hs, ?_⟩
  change d.nlink.toNat = 0
  change (d.nlink.toNat : Int) = 0 at hn
  omega

theorem ireg_mult_at_zero (ty : Int) : ireg_mult_at 0 ty = 0 := by simp [ireg_mult_at]
theorem ireg_mult_at_ge (n : Nat) (ty : Int) : n ≤ ireg_mult_at n ty := by
  unfold ireg_mult_at; split <;> omega
theorem ireg_mult_at_le (n : Nat) (ty : Int) : ireg_mult_at n ty ≤ n + 1 := by
  unfold ireg_mult_at; split <;> omega

theorem ireg_mult_zero (d : Dinode) (h : d.nlinkZ = 0) : ireg_mult d = 0 := by
  have hn : ireg_nl d = 0 := by simpa [ireg_nl, InodeRegionImage.nlink, Dinode.nlinkZ] using h
  simp [ireg_mult, hn, ireg_mult_at_zero]

theorem ireg_mult_nl (d : Dinode) : ireg_nl d ≤ ireg_mult d ∧ ireg_mult d ≤ ireg_nl d + 1 :=
  ⟨ireg_mult_at_ge _ _, ireg_mult_at_le _ _⟩

theorem ireg_dot_delta_not_dir (ty n : Int) (h : ty ≠ 1) : ireg_dot_delta ty n = 1 := by
  simp [ireg_dot_delta, h]
theorem ireg_dot_delta_live (ty n : Int) (h : n ≠ 0) : ireg_dot_delta ty n = 1 := by
  simp [ireg_dot_delta, h]

theorem ireg_mult_bump (d d' : Dinode) (hn : d'.nlinkZ = d.nlinkZ + 1)
    (ht : d'.typeZ = d.typeZ) :
    ireg_mult d' = ireg_mult d + ireg_dot_delta d.typeZ d.nlinkZ := by
  have step : d'.nlink.toNat = d.nlink.toNat + 1 := by
    change (d'.nlink.toNat : Int) = (d.nlink.toNat : Int) + 1 at hn
    omega
  unfold ireg_mult ireg_mult_at ireg_dot_delta
  rw [ht]
  simp only [ireg_nl, InodeRegionImage.nlink, Dinode.nlinkZ]
  by_cases ty : d.typeZ = 1 <;> by_cases nz : d.nlink.toNat = 0 <;> simp [ty, nz, step]

theorem ireg_mult_drop (d d' : Dinode) (hn : d.nlinkZ = d'.nlinkZ + 1)
    (ht : d'.typeZ = d.typeZ) :
    ireg_mult d = ireg_mult d' + ireg_dot_delta d'.typeZ d'.nlinkZ :=
  ireg_mult_bump d' d hn ht.symm

theorem ireg_reg_ok_ex (ty : Int) : ∃ v, ireg_reg_ok ty v := by
  by_cases h : ty = 1
  · exact ⟨.directory 0, h⟩
  · exact ⟨.file, h⟩

end MachCSL.Logic.IcacheInodeCustody
