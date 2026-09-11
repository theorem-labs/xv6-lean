import MachCSL.Logic.SpinlockProtocolInit

namespace MachCSL.Logic.SpinlockProtocol
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem bundle_word (era : Era.Record) (g : State) (a : PhysicalAddress) (v : BitVec 32) (t : Nat) :
    iprop(⊢ MemoryExclusiveWP.readBundle capacity.machine.era era g -∗
      wordAt capacity era a v t -∗ ⌜readBytes g.memory a 4 = some v⌝) := by
  unfold MemoryExclusiveWP.readBundle
  iintro ⟨_, Hheap, _⟩ Hword
  iapply word_current capacity era g a v t $$ Hheap Hword

theorem body_current (era : Era.Record) (γ : GName) (g : State) :
    iprop(⊢ body capacity era γ -∗ MemoryExclusiveWP.readBundle capacity.machine.era era g -∗
      ⌜∃ word : BitVec 32, (word = 0#32 ∨ word = 1#32) ∧
        readBytes g.memory SpinlockImage.lockAddress 4 = some word⌝) := by
  unfold body
  iintro ⟨%B, %time, Hbody⟩ Hbundle
  icases Hbody with (Hfree | Hheld)
  · icases Hfree with ⟨Hword, _⟩
    ihave %read := bundle_word capacity era g SpinlockImage.lockAddress 0#32 time $$ Hbundle Hword
    ipureintro
    exact ⟨0#32, Or.inl rfl, read⟩
  · icases Hheld with ⟨%owner, Hword, _⟩
    ihave %read := bundle_word capacity era g SpinlockImage.lockAddress 1#32 time $$ Hbundle Hword
    ipureintro
    exact ⟨1#32, Or.inr rfl, read⟩

variable {hlc : HasLC} [InvGS_gen hlc GF]

theorem invariant_current (N : Namespace) (era : Era.Record) (γ : GName) (g : State) :
    iprop(⊢ isLock capacity N era γ -∗ MemoryExclusiveWP.readBundle capacity.machine.era era g ={⊤}=∗
      MemoryExclusiveWP.readBundle capacity.machine.era era g ∗
      ⌜∃ word : BitVec 32, (word = 0#32 ∨ word = 1#32) ∧
        readBytes g.memory SpinlockImage.lockAddress 4 = some word⌝) := by
  iintro #Hinv Hbundle
  iunfold isLock at Hinv
  iunfold inv at Hinv
  imod Hinv $$ %(⊤ : CoPset) [] with ⟨Hbody, Hclose⟩
  · ipureintro; exact fun _ _ => CoPset.mem_full
  · imod Hbody
    ihave %current := body_current capacity era γ g $$ Hbody Hbundle
    imod Hclose $$ [Hbody] with _
    · iintro !>; iexact Hbody
    · imodintro
      iframe Hbundle
      ipureintro
      exact current

theorem exclusive_access (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (N : Namespace) (γ : GName) (cpu : CPU) :
    EventPlan.ExclusiveAccess capacity.machine era cpu relations
      (resource capacity fixed gen era N γ cpu) := by
  intro phase n req enabled
  obtain ⟨rfl, same⟩ := enabled
  cases same
  unfold resource payload
  iintro ⟨#Hcert, #Hinv, _⟩ %g Hbundle Htso Hview
  imod invariant_current capacity N era γ g $$ Hinv Hbundle with ⟨Hbundle, %current⟩
  obtain ⟨word, binary, read⟩ := current
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  iexists word
  isplit
  · ipureintro; exact read
  · iintro !>
    imod Hback
    imodintro
    iframe Hbundle Htso
    iexists (Phase.reserved word)
    isplit
    · ipureintro; exact ExclusiveStep.reserve word binary
    · dsimp only
      iframe Hcert Hinv
      ipureintro
      exact binary
theorem plain_access (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (N : Namespace) (γ : GName) (cpu : CPU) :
    EventPlan.PlainAccess capacity.machine fixed gen era cpu relations
      (resource capacity fixed gen era N γ cpu) := by
  intro phase n req enabled
  obtain ⟨word, next, step⟩ := enabled
  cases step with
  | load B v t =>
    unfold resource payload won
    iintro ⟨#Hcert, #Hinv, ⟨Hfrag, #Hview, %positive, #Hreceipt⟩, Hword, %bound⟩ %g %live Hpower
    ihave Hvisible := Tso.Views.viewLB_le capacity.machine.era.views era.views era.logLength
      (hartAgent cpu) B t bound $$ Hview
    ihave %visible := word_visible capacity fixed g gen era live cpu SpinlockImage.counterAddress v t $$
      Hpower Hcert Hword Hvisible
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      intro view above _
      exact ⟨v, visible view above, Phase.loaded B v t, PlainStep.load B v t⟩
    · iintro !>
      imod Hback
      imodintro
      iframe Hpower
      iintro %view %returned %lower %upper %actual %allowed Hreceipt'
      obtain ⟨next, related⟩ := allowed
      cases related
      iexists (Phase.loaded B v t)
      isplit
      · ipureintro; exact PlainStep.load B v t
      · dsimp only
        iframe Hcert Hinv Hfrag Hview Hreceipt Hword
        isplit <;> ipureintro
        · exact positive
        · exact bound

end MachCSL.Logic.SpinlockProtocol
