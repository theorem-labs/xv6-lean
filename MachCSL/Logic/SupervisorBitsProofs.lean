import MachCSL.Logic.SupervisorBitsSpec

namespace MachCSL.Logic.SupervisorBits
open Iris Iris.BI Iris.ProofMode MachCSL.Machine LeanPaperStock.Functions

theorem half_add_half : half + half = 1 := Qp.half_add_half 1
theorem quarter_add_quarter : quarter + quarter = half := Qp.half_add_half half
theorem eighth_add_eighth : eighth + eighth = quarter := Qp.half_add_half quarter

variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem split (name : GName) (q₁ q₂ : Qp) (value : Bit) :
    iprop(⊢ bit capacity name (q₁ + q₂) value -∗
      bit capacity name q₁ value ∗ bit capacity name q₂ value) := by
  letI := capacity.bits
  exact ghost_var_split name value q₁ q₂

theorem agree (name : GName) (q₁ q₂ : Qp) (a b : Bit) :
    iprop(⊢ bit capacity name q₁ a -∗ bit capacity name q₂ b -∗ ⌜a = b⌝) := by
  letI := capacity.bits
  exact ghost_var_agree name a (.own q₁) b (.own q₂)

private theorem allocate_halves (value : Bit) :
    iprop(⊢ |==> ∃ name, bit capacity name half value ∗ bit capacity name half value) := by
  letI := capacity.bits
  imod ghost_var_alloc value with ⟨%name, H⟩
  iexists name
  imodintro
  have cut := split capacity name half half value
  rw [half_add_half] at cut
  unfold bit at cut
  unfold bit
  iapply cut $$ H

theorem allocate (value : Bit) :
    iprop(⊢ |==> ∃ name, bit capacity name half value ∗
      bit capacity name quarter value ∗ bit capacity name quarter value) := by
  imod allocate_halves capacity value with ⟨%name, Hhalf, Hrest⟩
  iunfold bit at Hrest
  have cut := split capacity name quarter quarter value
  rw [quarter_add_quarter] at cut
  unfold bit at cut
  ihave ⟨Hcode, Hhandler⟩ := cut $$ Hrest
  iexists name
  imodintro
  iframe
  unfold bit
  iframe

theorem flip (name : GName) (a b c value : Bit) :
    iprop(⊢ bit capacity name half a -∗ bit capacity name quarter b -∗
      bit capacity name quarter c ==∗ bit capacity name half value ∗
        bit capacity name quarter value ∗ bit capacity name quarter value) := by
  letI := capacity.bits
  unfold bit
  iintro Hhalf Hcode Hhandler
  icombine Hcode Hhandler as Hrest
  ieval (rewrite [quarter_add_quarter]) at Hrest
  imod ghost_var_update_2 value name a half b half half_add_half $$ Hhalf Hrest with ⟨Hhalf, Hrest⟩
  have cut := split capacity name quarter quarter value
  rw [quarter_add_quarter] at cut
  unfold bit at cut
  ihave ⟨Hcode, Hhandler⟩ := cut $$ Hrest
  imodintro
  iframe

theorem flip_four (name : GName) (a b c d : Bit) (enabled : Bool) :
    iprop(⊢ bit capacity name half a -∗ bit capacity name eighth b -∗
      bit capacity name eighth c -∗ bit capacity name quarter d ==∗
      bit capacity name half (sieBit enabled) ∗ bit capacity name eighth (sieBit enabled) ∗
      bit capacity name eighth (sieBit enabled) ∗ bit capacity name quarter (sieBit enabled)) := by
  letI := capacity.bits
  unfold bit
  iintro Hhalf Harm Hcount Hhandler
  icombine Harm Hcount as Hcode
  ieval (rewrite [eighth_add_eighth]) at Hcode
  have update := flip capacity name a b d (sieBit enabled)
  unfold bit at update
  imod update $$ Hhalf Hcode Hhandler with ⟨Hhalf, Hcode, Hhandler⟩
  have cut := split capacity name eighth eighth (sieBit enabled)
  rw [eighth_add_eighth] at cut
  unfold bit at cut
  ihave ⟨Harm, Hcount⟩ := cut $$ Hcode
  imodintro
  iframe

theorem sret_agree (names : Names) (a b a' b' : Bit) :
    iprop(⊢ sretBits capacity names a b -∗ sretBits capacity names a' b' -∗
      ⌜a = a' ∧ b = b'⌝) := by
  unfold sretBits
  iintro ⟨Ha, Hb⟩ ⟨Ha', Hb'⟩
  ihave %ha := agree capacity names.spp half half a a' $$ Ha Ha'
  ihave %hb := agree capacity names.spie half half b b' $$ Hb Hb'
  ipureintro
  exact ⟨ha, hb⟩

theorem sret_update (names : Names) (a b a' b' wa wb : Bit) :
    iprop(⊢ sretBits capacity names a b -∗ sretBits capacity names a' b' ==∗
      sretBits capacity names wa wb ∗ sretBits capacity names wa wb) := by
  letI := capacity.bits
  unfold sretBits bit
  iintro ⟨Ha, Hb⟩ ⟨Ha', Hb'⟩
  imod ghost_var_update_2 wa names.spp a half a' half half_add_half $$ Ha Ha' with ⟨Ha, Ha'⟩
  imod ghost_var_update_2 wb names.spie b half b' half half_add_half $$ Hb Hb' with ⟨Hb, Hb'⟩
  imodintro
  iframe

theorem tie_congr (names : Names) (ms ms' : BitVec 64)
    (spp : _get_Mstatus_SPP ms' = _get_Mstatus_SPP ms)
    (spie : _get_Mstatus_SPIE ms' = _get_Mstatus_SPIE ms) :
    iprop(⊢ sretTie capacity names ms -∗ sretTie capacity names ms') := by
  unfold sretTie
  rw [spp, spie]
  iintro H
  iexact H

theorem attach (registerName : GName) (ms : BitVec 64) (facts : MsFacts ms) :
    iprop(⊢ Registers.regPointsto capacity.registers registerName .mstatus (.own 1) ms ==∗
      ∃ names, msOwn capacity registerName names ms ∗ allocationRemainder capacity names ms) := by
  iintro Hregister
  imod allocate capacity (_get_Mstatus_SIE ms) with ⟨%sie, Hhalf, Hcode, Hhandler⟩
  imod allocate_halves capacity (_get_Mstatus_SPP ms) with ⟨%spp, Hspp, Hspp'⟩
  imod allocate_halves capacity (_get_Mstatus_SPIE ms) with ⟨%spie, Hspie, Hspie'⟩
  iunfold bit at Hcode
  have cut := split capacity sie eighth eighth (_get_Mstatus_SIE ms)
  rw [eighth_add_eighth] at cut
  unfold bit at cut
  ihave ⟨Harm, Hcount⟩ := cut $$ Hcode
  iexists (Names.mk sie spp spie)
  imodintro
  unfold msOwn allocationRemainder sretTie sretBits
  iframe
  unfold bit
  iframe
  ipureintro
  exact facts

theorem live_bit (registerName : GName) (names : Names) (ms : BitVec 64) (enabled : Bool) :
    iprop(⊢ msOwn capacity registerName names ms -∗ armBit capacity names enabled -∗
      ⌜_get_Mstatus_SIE ms = sieBit enabled⌝) := by
  unfold msOwn armBit
  iintro ⟨_, Hhalf, _, _⟩ Harm
  iapply agree capacity names.sie half eighth _ _ $$ Hhalf Harm

theorem off (registerName : GName) (names : Names) (ms : BitVec 64) :
    iprop(⊢ msOwn capacity registerName names ms -∗ offToken capacity names -∗
      ⌜(_get_Mstatus_SIE ms == 1#1) = false⌝) := by
  unfold offToken
  iintro Hms Hoff
  ihave %equal := live_bit capacity registerName names ms false $$ Hms Hoff
  ipureintro
  rw [equal]
  rfl

theorem sieBit_injective : Function.Injective sieBit := by
  intro a b h
  cases a <;> cases b <;> simp_all [sieBit]

theorem count_index (names : Names) (depth : Nat) (baseEnabled enabled : Bool) :
    iprop(⊢ armBit capacity names enabled -∗ countBit capacity names depth baseEnabled -∗
      ⌜(if depth = 0 then baseEnabled else false) = enabled⌝) := by
  unfold armBit countBit
  iintro Harm Hcount
  ihave %equal := agree capacity names.sie eighth eighth _ _ $$ Harm Hcount
  ipureintro
  by_cases zero : depth = 0
  · simp only [zero, ite_true] at equal ⊢
    exact (sieBit_injective equal).symm
  · simp only [zero, ite_false] at equal ⊢
    exact (sieBit_injective (a₂ := false) equal).symm

theorem actual : Spec capacity where
  split := split capacity
  agree := agree capacity
  allocate := allocate capacity
  flip := flip capacity
  flipFour := flip_four capacity
  sretAgree := sret_agree capacity
  sretUpdate := sret_update capacity
  tieCongr := tie_congr capacity
  attach := attach capacity
  liveBit := live_bit capacity
  off := off capacity
  countIndex := count_index capacity

end MachCSL.Logic.SupervisorBits
