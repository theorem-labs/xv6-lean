import Xv6.Kernel.SieOffCapabilitySpec
import Xv6.Kernel.SupervisorTranslationLink
import Xv6.Kernel.SconfLink
import Xv6.Kernel.KernelStackLink
import MachCSL.Logic.TimerCapLink

namespace Xv6.Kernel.SieOffCapability
open Iris Iris.BI MachCSL.Machine MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance witness_persistent era cpu tier : Persistent (tierWitness capacity era cpu tier) := by
  cases tier <;> unfold tierWitness <;> infer_instance

theorem witness_identity era cpu : iprop(⊢ tierWitness capacity era cpu .identity) := by
  unfold tierWitness
  iempintro

theorem witness_receipt era cpu tier :
    iprop(SupervisorTranslation.kptOn capacity.translation era cpu ⊢ tierWitness capacity era cpu tier) := by
  cases tier
  · iintro _
    iapply witness_identity
  · exact .rfl

variable {hlc : HasLC} [InvGS_gen hlc GF]

instance timer_persistent era cpu : Persistent (timer capacity era cpu) := by
  unfold timer
  infer_instance

theorem intro_cap era cpu tier ξ file available :
    iprop(⊢ stack capacity era tier ξ (sp file) available -∗
      SupervisorTranslation.sourceSlot capacity.translation era cpu -∗ off capacity era cpu -∗
      running capacity era cpu ξ -∗ timer capacity era cpu -∗ tierWitness capacity era cpu tier -∗
      cap capacity era cpu tier ξ file available) := by
  simp only [cap, rest, trapReserve, Nat.zero_add]
  iintro Hstk Htr Hoff Hrun Htimer Hwit
  iframe

theorem intro_bare era cpu ξ file available value :
    iprop(⊢ stack capacity era .identity ξ (sp file) available -∗
      SupervisorTranslation.pending capacity.translation era cpu -∗
      SupervisorTranslation.bare capacity.translation era cpu -∗ Sconf.cell capacity era cpu .stvec value -∗
      running capacity era cpu ξ -∗ off capacity era cpu -∗ timer capacity era cpu -∗
      cap capacity era cpu .identity ξ file available) := by
  iintro Hstk Hpending Hbare Hstvec Hrun Hoff Htimer
  iapply intro_cap capacity era cpu .identity ξ file available $$ Hstk [Hpending Hbare Hstvec] Hoff Hrun Htimer []
  · iapply (SupervisorTranslation.nativeSpec capacity.translation).intro_bare $$ Hpending Hbare Hstvec
  · iapply witness_identity

theorem open_cap era cpu tier ξ file available :
    iprop(cap capacity era cpu tier ξ file available ⊣⊢
      stack capacity era tier ξ (sp file) available ∗ rest capacity era cpu tier ξ) := by
  simp only [cap, trapReserve, Nat.zero_add]
  exact .rfl

theorem witness_access era cpu tier ξ file available :
    iprop(cap capacity era cpu tier ξ file available ⊢
      cap capacity era cpu tier ξ file available ∗ tierWitness capacity era cpu tier) := by
  unfold cap rest
  iintro ⟨Hstk, Htr, Hoff, Hrun, Htimer, #Hwit⟩
  iframe Hstk Htr Hoff Hrun Htimer Hwit

theorem timer_access era cpu tier ξ file available :
    iprop(cap capacity era cpu tier ξ file available ⊢
      timer capacity era cpu ∗ cap capacity era cpu tier ξ file available) := by
  unfold cap rest
  iintro ⟨Hstk, Htr, Hoff, Hrun, #Htimer, Hwit⟩
  iframe Hstk Htr Hoff Hrun Htimer Hwit

theorem tier_up era cpu tier tier' ξ file available (le : KernelDatum.Tier.Le tier tier') :
    iprop(⊢ cap capacity era cpu tier ξ file available -∗
      SupervisorTranslation.kptOn capacity.translation era cpu -∗ cap capacity era cpu tier' ξ file available) := by
  unfold cap rest
  iintro ⟨Hstk, Htr, Hoff, Hrun, Htimer, _⟩ Hon
  ihave Hstk := (KernelStack.nativeSpec capacity.translation).mono era tier tier' ξ _ _ le $$ Hstk
  iframe Hstk Htr Hoff Hrun Htimer
  iapply witness_receipt capacity era cpu tier' $$ Hon

theorem retarget era cpu tier ξ file file' available (same : sp file = sp file') :
    iprop(cap capacity era cpu tier ξ file available ⊢ cap capacity era cpu tier ξ file' available) := by
  unfold cap
  rw [same]

theorem push era cpu tier ξ file file' available k
    (bound : k ≤ available) (moved : sp file' = KernelStack.paStk (sp file) k) :
    iprop(cap capacity era cpu tier ξ file available ⊢
      cap capacity era cpu tier ξ file' (available - k) ∗ stack capacity era tier ξ (sp file) k) := by
  simp only [cap, trapReserve, Nat.zero_add]
  iintro ⟨Hstk, Hrest⟩
  ihave ⟨Htop, Hdeep⟩ := ((KernelStack.nativeSpec capacity.translation).split era tier ξ (sp file) k available bound).mp $$ Hstk
  rw [moved]
  iframe

theorem pop era cpu tier ξ file file' available k
    (moved : sp file = KernelStack.paStk (sp file') k) :
    iprop(⊢ stack capacity era tier ξ (sp file') k -∗ cap capacity era cpu tier ξ file available -∗
      cap capacity era cpu tier ξ file' (available + k)) := by
  simp only [cap, trapReserve, Nat.zero_add]
  iintro Htop ⟨Hdeep, Hrest⟩
  iframe Hrest
  rw [Nat.add_comm available k]
  iapply ((KernelStack.nativeSpec capacity.translation).append era tier ξ (sp file') k available).mpr
  rw [← moved]
  iframe

theorem grow era cpu tier ξ file available k :
    iprop(⊢ stack capacity era tier ξ (KernelStack.paStk (sp file) available) k -∗
      cap capacity era cpu tier ξ file available -∗ cap capacity era cpu tier ξ file (available + k)) := by
  simp only [cap, trapReserve, Nat.zero_add]
  iintro Hdeep ⟨Htop, Hrest⟩
  iframe Hrest
  iapply ((KernelStack.nativeSpec capacity.translation).append era tier ξ (sp file) available k).mpr
  iframe

theorem shrink era cpu tier ξ file available k (bound : k ≤ available) :
    iprop(cap capacity era cpu tier ξ file available ⊢ cap capacity era cpu tier ξ file (available - k) ∗
      stack capacity era tier ξ (KernelStack.paStk (sp file) (available - k)) k) := by
  simp only [cap, trapReserve, Nat.zero_add]
  iintro ⟨Hstk, Hrest⟩
  have decomposition : available = (available - k) + k := by omega
  have law := (KernelStack.nativeSpec capacity.translation).append era tier ξ (sp file) (available - k) k
  rw [← decomposition] at law
  ihave ⟨Htop, Hdeep⟩ := law.mp $$ Hstk
  iframe

theorem two_words era cpu tier ξ file available (bound : 2 ≤ available) :
    iprop(cap capacity era cpu tier ξ file available ⊢ ∃ first second : BitVec 64,
      KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk (sp file) 1) (.own 1) first ∗
      KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk (sp file) 2) (.own 1) second ∗
      (∀ first' : BitVec 64, ∀ second' : BitVec 64,
        KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk (sp file) 1) (.own 1) first' -∗
        KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk (sp file) 2) (.own 1) second' -∗
        cap capacity era cpu tier ξ file available)) := by
  simp only [cap, trapReserve, Nat.zero_add]
  iintro ⟨Hstk, Hrest⟩
  have law := (KernelStack.nativeSpec capacity.translation).frame_two era tier ξ (sp file) available bound
  ihave ⟨%first, %second, Hfirst, Hsecond, Hdeep⟩ := law.mp $$ Hstk
  iexists first, second
  iframe Hfirst Hsecond
  iintro %first' %second' Hfirst Hsecond
  iframe Hrest
  iapply law.mpr
  iexists first', second'
  iframe

theorem gpr_open fixed gen era cpu tier ξ file available :
    iprop(gpr capacity fixed gen era cpu tier ξ file available ⊣⊢
      active capacity era cpu ∗ Sconf.sconf capacity fixed gen era cpu ∗
      cap capacity era cpu tier ξ file available ∗
      HartTp.pinnedFile capacity.machine.era.registers era cpu file) := .rfl

theorem gpr_intro fixed gen era cpu tier ξ file available :
    iprop(⊢ active capacity era cpu -∗ Sconf.sconf capacity fixed gen era cpu -∗
      cap capacity era cpu tier ξ file available -∗
      HartTp.pinnedFile capacity.machine.era.registers era cpu file -∗
      gpr capacity fixed gen era cpu tier ξ file available) := by
  unfold gpr
  iintro Hactive Hconf Hcap Hfile
  iframe

theorem gpr_at_open fixed gen era cpu tier ξ file available :
    iprop(gpr capacity fixed gen era cpu tier ξ file available ⊢ ∃ ms,
      gprAt capacity fixed gen era cpu tier ξ ms file available) := by
  unfold gpr gprAt
  iintro ⟨Hactive, Hconf, Hcap, Hfile⟩
  ihave ⟨%ms, Hat⟩ := (Sconf.nativeSpec capacity).at_open fixed gen era cpu $$ Hconf
  iexists ms
  iframe

theorem gpr_at_close fixed gen era cpu tier ξ ms file available :
    iprop(gprAt capacity fixed gen era cpu tier ξ ms file available ⊢
      gpr capacity fixed gen era cpu tier ξ file available) := by
  unfold gprAt gpr
  iintro ⟨Hactive, Hat, Hcap, Hfile⟩
  ihave Hconf := (Sconf.nativeSpec capacity).at_close fixed gen era cpu ms $$ Hat
  iframe

end Xv6.Kernel.SieOffCapability
