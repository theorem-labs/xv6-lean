import MachCSL.Logic.SupervisorBitsDefs

namespace MachCSL.Logic.SupervisorBits
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

/-- Proposed resource laws. No proof constructor or interrupt WP is assumed. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  split : ∀ name q₁ q₂ value, iprop(⊢ bit capacity name (q₁ + q₂) value -∗
    bit capacity name q₁ value ∗ bit capacity name q₂ value)
  agree : ∀ name q₁ q₂ value₁ value₂, iprop(⊢ bit capacity name q₁ value₁ -∗
    bit capacity name q₂ value₂ -∗ ⌜value₁ = value₂⌝)
  allocate : ∀ value, iprop(⊢ |==> ∃ name,
    bit capacity name half value ∗ bit capacity name quarter value ∗
      bit capacity name quarter value)
  flip : ∀ name a b c value, iprop(⊢ bit capacity name half a -∗
    bit capacity name quarter b -∗ bit capacity name quarter c ==∗
    bit capacity name half value ∗ bit capacity name quarter value ∗
      bit capacity name quarter value)
  flipFour : ∀ name a b c d enabled, iprop(⊢ bit capacity name half a -∗
    bit capacity name eighth b -∗ bit capacity name eighth c -∗
    bit capacity name quarter d ==∗
    bit capacity name half (sieBit enabled) ∗ bit capacity name eighth (sieBit enabled) ∗
    bit capacity name eighth (sieBit enabled) ∗ bit capacity name quarter (sieBit enabled))
  sretAgree : ∀ names a b a' b', iprop(⊢ sretBits capacity names a b -∗
    sretBits capacity names a' b' -∗ ⌜a = a' ∧ b = b'⌝)
  sretUpdate : ∀ names a b a' b' wa wb, iprop(⊢ sretBits capacity names a b -∗
    sretBits capacity names a' b' ==∗
      sretBits capacity names wa wb ∗ sretBits capacity names wa wb)
  tieCongr : ∀ names ms ms', _get_Mstatus_SPP ms' = _get_Mstatus_SPP ms →
    _get_Mstatus_SPIE ms' = _get_Mstatus_SPIE ms →
    iprop(⊢ sretTie capacity names ms -∗ sretTie capacity names ms')
  attach : ∀ registerName ms, MsFacts ms →
    iprop(⊢ Registers.regPointsto capacity.registers registerName .mstatus (.own 1) ms ==∗
      ∃ names, msOwn capacity registerName names ms ∗ allocationRemainder capacity names ms)
  liveBit : ∀ registerName names ms enabled,
    iprop(⊢ msOwn capacity registerName names ms -∗ armBit capacity names enabled -∗
      ⌜_get_Mstatus_SIE ms = sieBit enabled⌝)
  off : ∀ registerName names ms,
    iprop(⊢ msOwn capacity registerName names ms -∗ offToken capacity names -∗
      ⌜(_get_Mstatus_SIE ms == 1#1) = false⌝)
  countIndex : ∀ names depth baseEnabled enabled,
    iprop(⊢ armBit capacity names enabled -∗ countBit capacity names depth baseEnabled -∗
      ⌜(if depth = 0 then baseEnabled else false) = enabled⌝)

end MachCSL.Logic.SupervisorBits
