import Xv6.Kernel.KernelDatumSpec
import MachCSL.Logic.KptGhostLink
import MachCSL.Logic.TsoContextProofs

namespace Xv6.Kernel.KernelDatum
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

theorem order_cases tier tier' (le : Tier.Le tier tier') :
    tier = tier' ∨ (tier = .identity ∧ tier' = .full) := by
  cases tier <;> cases tier' <;> simp_all [Tier.Le]

theorem pin_mono tier tier' ppn va (le : Tier.Le tier tier') (pin : Pin tier ppn va) :
    Pin tier' ppn va := by
  cases tier <;> cases tier' <;> simp_all [Tier.Le, Pin]

theorem pin_identity ppn va (pin : Pin .identity ppn va) : physical ppn va = va := pin

theorem pin_intro tier ppn va (same : physical ppn va = va) : Pin tier ppn va := by
  cases tier <;> simp_all [Pin]

theorem canonical va (positive : Positive va) : va = (va.extractLsb' 0 39).signExtend 64 := by
  have bound : va.toNat < 2^38 := positive
  have small : (va.extractLsb' 0 39).toNat = va.toNat := by
    simp [BitVec.extractLsb'_toNat, Nat.mod_eq_of_lt (show va.toNat < 2^39 by omega)]
  have msb : (va.extractLsb' 0 39).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [small]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp [small, Nat.mod_eq_of_lt va.isLt]

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance claim_persistent era tier va ppn : Persistent (claim capacity era tier va ppn) := by
  unfold claim
  infer_instance

instance claim_timeless era tier va ppn : Timeless (claim capacity era tier va ppn) := by
  unfold claim
  infer_instance

theorem claim_agree era tier tier' va ppn ppn' :
    iprop(⊢ claim capacity era tier va ppn -∗ claim capacity era tier' va ppn' -∗ ⌜ppn = ppn'⌝) := by
  unfold claim
  iintro ⟨Hmap,_⟩ ⟨Hmap',_⟩
  ihave %same := (KptGhost.nativeSpec capacity.ghost).mapAgree era.kernelMap (vpn va) ppn ppn' .rw .rw
    $$ [Hmap Hmap']
  · iframe Hmap Hmap'
  · ipureintro
    exact same.1

theorem claim_mono era tier tier' va ppn (le : Tier.Le tier tier') :
    iprop(claim capacity era tier va ppn ⊢ claim capacity era tier' va ppn) := by
  unfold claim
  iintro ⟨Hmap,%facts⟩
  iframe Hmap
  ipureintro
  exact ⟨facts.1,facts.2.1,pin_mono tier tier' ppn va le facts.2.2⟩

theorem access era tier ξ va dq value :
    iprop(byte capacity era tier ξ va dq value ⊢ ∃ ppn,
      claim capacity era tier va ppn ∗ physicalByte capacity era ξ (physical ppn va) dq value ∗
      (∀ newValue, physicalByte capacity era ξ (physical ppn va) dq newValue -∗
        byte capacity era tier ξ va dq newValue)) := by
  unfold byte
  iintro ⟨%ppn,#Hclaim,Hbyte⟩
  iexists ppn
  iframe Hclaim Hbyte
  iintro %newValue Hbyte
  iexists ppn
  iframe Hclaim Hbyte

theorem agree era tier tier' ξ ξ' va dq dq' value value' :
    iprop(⊢ byte capacity era tier ξ va dq value -∗ byte capacity era tier' ξ' va dq' value' -∗
      ⌜value = value'⌝) := by
  unfold byte
  iintro ⟨%ppn,Hclaim,Hbyte⟩ ⟨%ppn',Hclaim',Hbyte'⟩
  ihave %same := claim_agree capacity era tier tier' va ppn ppn' $$ Hclaim Hclaim'
  subst ppn'
  unfold physicalByte TsoContext.physPointsto
  icases Hbyte with ⟨%time,Hbyte,_⟩
  icases Hbyte' with ⟨%time',Hbyte',_⟩
  iapply Tso.physBytePointsto_agree
    (TsoContextReadWP.contextCapacity capacity.machine).heap.ledger
    (TsoContextReadWP.contextNames era).tso.ledger.bytes
    (physical ppn va) dq dq' value value' $$ [Hbyte Hbyte']
  iframe Hbyte Hbyte'

theorem mono era tier tier' ξ va dq value (le : Tier.Le tier tier') :
    iprop(byte capacity era tier ξ va dq value ⊢ byte capacity era tier' ξ va dq value) := by
  unfold byte
  iintro ⟨%ppn,Hclaim,Hbyte⟩
  iexists ppn
  iframe Hbyte
  iapply claim_mono capacity era tier tier' va ppn le $$ Hclaim

theorem identity_access era ξ va dq value :
    iprop(byte capacity era .identity ξ va dq value ⊢
      physicalByte capacity era ξ va dq value ∗
      (∀ newValue, physicalByte capacity era ξ va dq newValue -∗
        byte capacity era .identity ξ va dq newValue)) := by
  iintro Hbyte
  ihave Haccess := access capacity era .identity ξ va dq value $$ Hbyte
  icases Haccess with ⟨%ppn,Hclaim,Hbyte,Hclose⟩
  iunfold claim at Hclaim
  icases Hclaim with ⟨_,%facts⟩
  have same : physical ppn va = va := facts.2.2
  isimp only [same] at Hbyte Hclose
  iframe Hbyte Hclose

theorem word_mono era tier tier' ξ va dq value (le : Tier.Le tier tier') :
    iprop(word capacity era tier ξ va dq value ⊢ word capacity era tier' ξ va dq value) := by
  unfold word
  iintro ⟨Halign,Hbytes⟩
  iframe Halign
  iapply BigSepL.bigSepL_mono (fun {_ j} _ =>
    mono capacity era tier tier' ξ (addressAdd va j) dq (nthByte value j) le) $$ Hbytes

theorem actual : Spec capacity :=
  ⟨claim_agree capacity,claim_mono capacity,access capacity,agree capacity,
    mono capacity,identity_access capacity,word_mono capacity⟩

end Xv6.Kernel.KernelDatum
