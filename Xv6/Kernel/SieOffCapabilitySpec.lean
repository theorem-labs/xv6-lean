import Xv6.Kernel.SieOffCapabilityDefs

namespace Xv6.Kernel.SieOffCapability
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  witness_persistent : ∀ era cpu tier, Persistent (tierWitness capacity era cpu tier)
  witness_identity : ∀ era cpu, iprop(⊢ tierWitness capacity era cpu .identity)
  witness_receipt : ∀ era cpu tier,
    iprop(SupervisorTranslation.kptOn capacity.translation era cpu ⊢ tierWitness capacity era cpu tier)
  intro : ∀ era cpu tier ξ file available,
    iprop(⊢ stack capacity era tier ξ (sp file) available -∗
      SupervisorTranslation.sourceSlot capacity.translation era cpu -∗ off capacity era cpu -∗
      running capacity era cpu ξ -∗ timer capacity era cpu -∗ tierWitness capacity era cpu tier -∗
      cap capacity era cpu tier ξ file available)
  intro_bare : ∀ era cpu ξ file available value,
    iprop(⊢ stack capacity era .identity ξ (sp file) available -∗
      SupervisorTranslation.pending capacity.translation era cpu -∗
      SupervisorTranslation.bare capacity.translation era cpu -∗ Sconf.cell capacity era cpu .stvec value -∗
      running capacity era cpu ξ -∗ off capacity era cpu -∗ timer capacity era cpu -∗
      cap capacity era cpu .identity ξ file available)
  open_cap : ∀ era cpu tier ξ file available,
    iprop(cap capacity era cpu tier ξ file available ⊣⊢
      stack capacity era tier ξ (sp file) available ∗ rest capacity era cpu tier ξ)
  witness_access : ∀ era cpu tier ξ file available,
    iprop(cap capacity era cpu tier ξ file available ⊢
      cap capacity era cpu tier ξ file available ∗ tierWitness capacity era cpu tier)
  timer_access : ∀ era cpu tier ξ file available,
    iprop(cap capacity era cpu tier ξ file available ⊢
      timer capacity era cpu ∗ cap capacity era cpu tier ξ file available)
  tier_up : ∀ era cpu tier tier' ξ file available, KernelDatum.Tier.Le tier tier' →
    iprop(⊢ cap capacity era cpu tier ξ file available -∗
      SupervisorTranslation.kptOn capacity.translation era cpu -∗ cap capacity era cpu tier' ξ file available)
  retarget : ∀ era cpu tier ξ file file' available, sp file = sp file' →
    iprop(cap capacity era cpu tier ξ file available ⊢ cap capacity era cpu tier ξ file' available)
  push : ∀ era cpu tier ξ file file' available k,
    k ≤ available → sp file' = KernelStack.paStk (sp file) k →
    iprop(cap capacity era cpu tier ξ file available ⊢
      cap capacity era cpu tier ξ file' (available - k) ∗ stack capacity era tier ξ (sp file) k)
  pop : ∀ era cpu tier ξ file file' available k,
    sp file = KernelStack.paStk (sp file') k →
    iprop(⊢ stack capacity era tier ξ (sp file') k -∗ cap capacity era cpu tier ξ file available -∗
      cap capacity era cpu tier ξ file' (available + k))
  grow : ∀ era cpu tier ξ file available k,
    iprop(⊢ stack capacity era tier ξ (KernelStack.paStk (sp file) available) k -∗
      cap capacity era cpu tier ξ file available -∗ cap capacity era cpu tier ξ file (available + k))
  shrink : ∀ era cpu tier ξ file available k, k ≤ available →
    iprop(cap capacity era cpu tier ξ file available ⊢ cap capacity era cpu tier ξ file (available - k) ∗
      stack capacity era tier ξ (KernelStack.paStk (sp file) (available - k)) k)
  two_words : ∀ era cpu tier ξ file available, 2 ≤ available →
    iprop(cap capacity era cpu tier ξ file available ⊢ ∃ first second : BitVec 64,
      KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk (sp file) 1) (.own 1) first ∗
      KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk (sp file) 2) (.own 1) second ∗
      (∀ first' : BitVec 64, ∀ second' : BitVec 64,
        KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk (sp file) 1) (.own 1) first' -∗
        KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk (sp file) 2) (.own 1) second' -∗
        cap capacity era cpu tier ξ file available))
  gpr_open : ∀ fixed gen era cpu tier ξ file available,
    iprop(gpr capacity fixed gen era cpu tier ξ file available ⊣⊢
      active capacity era cpu ∗ Sconf.sconf capacity fixed gen era cpu ∗
      cap capacity era cpu tier ξ file available ∗
      HartTp.pinnedFile capacity.machine.era.registers era cpu file)
  gpr_intro : ∀ fixed gen era cpu tier ξ file available,
    iprop(⊢ active capacity era cpu -∗ Sconf.sconf capacity fixed gen era cpu -∗
      cap capacity era cpu tier ξ file available -∗
      HartTp.pinnedFile capacity.machine.era.registers era cpu file -∗
      gpr capacity fixed gen era cpu tier ξ file available)
  gpr_at_open : ∀ fixed gen era cpu tier ξ file available,
    iprop(gpr capacity fixed gen era cpu tier ξ file available ⊢ ∃ ms,
      gprAt capacity fixed gen era cpu tier ξ ms file available)
  gpr_at_close : ∀ fixed gen era cpu tier ξ ms file available,
    iprop(gprAt capacity fixed gen era cpu tier ξ ms file available ⊢
      gpr capacity fixed gen era cpu tier ξ file available)

end Xv6.Kernel.SieOffCapability
