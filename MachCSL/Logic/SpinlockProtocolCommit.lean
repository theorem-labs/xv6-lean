import MachCSL.Logic.SpinlockProtocolStore

namespace MachCSL.Logic.SpinlockProtocol
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Basic ownership update at a real successful write. Its caller must keep
this body inside a guarded one-event invariant opening. -/
theorem commit [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (era : Era.Record) (γ : GName) (cpu : CPU) (g : State)
    (phase : Phase) (rr : Option Reservation) (n : Nat) (req : EventPlan.WriteRequest n)
    (value : BitVec (8 * n)) (mode : EventPlan.WriteMode n req rr)
    (eligible : ModeEnabled phase rr n req value mode) :
    iprop(⊢ body capacity era γ -∗ payload capacity era γ cpu phase -∗
      ⌜EventPlan.WriteFact mode g⌝ -∗
      MemoryWriteWP.writeBundle capacity.machine.era era g -∗
      Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes g ==∗
      body capacity era γ ∗
      MemoryWriteWP.writeBundle capacity.machine.era era (MemoryWriteWP.writeState g cpu req value) ∗
      Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes
        (MemoryWriteWP.writeState g cpu req value) ∗
      (Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu)
          (MemoryWriteWP.postView g cpu req) -∗
        ∃ next, ⌜WriteStep phase n req value next⌝ ∗ payload capacity era γ cpu next)) := by
  cases eligible with
  | swap old bound =>
    iintro Hbody Hpayload %oldRead Hbundle Htso
    change readBytes g.memory SpinlockImage.lockAddress 4 = some old at oldRead
    iunfold payload at Hpayload
    ihave %binary := Hpayload
    rcases binary with zero | one
    · subst old
      iunfold body at Hbody
      icases Hbody with ⟨%B, %time, (Hfree | Hheld)⟩
      · icases Hfree with ⟨Hword, Ha, Hfrag, %counter, %stamp, Hcounter⟩
        ihave %visible := word_timestamp_bound capacity era g SpinlockImage.counterAddress counter stamp $$ Htso Hcounter
        have store := store_word (hlc := hlc) capacity era g cpu swapWrite 0#32 1#32 time
        dsimp only [swapWrite, SpinlockAccess.writeRequest, SpinlockAccess.address] at store ⊢
        imod store $$ Hbundle Htso Hword with ⟨Hbundle, Htso, #Hreceipt, Hword⟩
        imod Lock.acquire_at capacity.lock γ cpu B (g.log.length + 1) $$ Ha Hfrag with ⟨Ha, Hfrag⟩
        imodintro
        isplitl [Ha Hword]
        · unfold body
          iexists (g.log.length + 1)
          iexists (g.log.length + 1)
          iright
          iexists cpu
          iframe Hword Ha
        · iframe Hbundle Htso
          iintro Hview
          iexists (Phase.held (g.log.length + 1) counter stamp)
          isplit
          · ipureintro
            exact WriteStep.acquire _ _ _ (by omega)
          · unfold payload won
            isimp only [MemoryWriteWP.postView, accessExclusive, varietyExclusive, ↓reduceIte] at Hview
            simp only [Nat.add_sub_cancel]
            iframe Hfrag Hview Hreceipt Hcounter
            isplit <;> ipureintro <;> omega
      · icases Hheld with ⟨%owner, Hword, Ha⟩
        ihave %read := bundle_word capacity era g SpinlockImage.lockAddress 1#32 time $$ Hbundle Hword
        have bad : (0#32 : BitVec 32) = 1#32 := Option.some.inj (oldRead.symm.trans read)
        exact False.elim ((by decide : (0#32 : BitVec 32) ≠ 1#32) bad)
    · subst old
      iunfold body at Hbody
      icases Hbody with ⟨%B, %time, (Hfree | Hheld)⟩
      · icases Hfree with ⟨Hword, _⟩
        ihave %read := bundle_word capacity era g SpinlockImage.lockAddress 0#32 time $$ Hbundle Hword
        have bad : (1#32 : BitVec 32) = 0#32 := Option.some.inj (oldRead.symm.trans read)
        exact False.elim ((by decide : (1#32 : BitVec 32) ≠ 0#32) bad)
      · icases Hheld with ⟨%owner, Hword, Ha⟩
        have store := store_word (hlc := hlc) capacity era g cpu swapWrite 1#32 1#32 time
        dsimp only [swapWrite, SpinlockAccess.writeRequest, SpinlockAccess.address] at store ⊢
        imod store $$ Hbundle Htso Hword with ⟨Hbundle, Htso, Hreceipt, Hword⟩
        imodintro
        isplitl [Ha Hword]
        · unfold body
          iexists B
          iexists (g.log.length + 1)
          iright
          iexists owner
          iframe Hword Ha
        · iframe Hbundle Htso
          iintro Hview
          iexists Phase.idle
          isplit
          · ipureintro; exact WriteStep.failed
          · unfold payload; itrivial
  | increment B v t rr =>
    iintro Hbody Hpayload _ Hbundle Htso
    iunfold payload at Hpayload
    icases Hpayload with ⟨Hwon, Hword, %visible⟩
    have store := store_word (hlc := hlc) capacity era g cpu (counterWrite (v + 1#32)) v (v + 1#32) t
    dsimp only [counterWrite, SpinlockAccess.writeRequest, SpinlockAccess.address] at store ⊢
    imod store $$ Hbundle Htso Hword with ⟨Hbundle, Htso, Hreceipt, Hword⟩
    imodintro
    iframe Hbody Hbundle Htso
    iintro Hview
    iexists (Phase.stored B (v + 1#32) (g.log.length + 1))
    isplit
    · ipureintro; exact WriteStep.increment B v t (g.log.length + 1)
    · unfold payload
      dsimp only
      iframe Hwon Hword
  | release B v t rr =>
    iintro Hbody Hpayload _ Hbundle Htso
    iunfold payload at Hpayload
    icases Hpayload with ⟨Hwon, Hcounter⟩
    iunfold won at Hwon
    icases Hwon with ⟨Hfrag, Hview, %positive, Hreceipt⟩
    iunfold body at Hbody
    icases Hbody with ⟨%oldPosition, %time, (Hfree | Hheld)⟩
    · icases Hfree with ⟨Hword, Ha, _⟩
      ihave %same := Lock.position_agree capacity.lock γ none (some (cpu, false)) oldPosition B $$ Ha Hfrag
      cases same.1
    · icases Hheld with ⟨%owner, Hword, Ha⟩
      ihave %same := Lock.position_agree capacity.lock γ (some (owner, false)) (some (cpu, false)) oldPosition B $$ Ha Hfrag
      have ownerEq : owner = cpu := congrArg Prod.fst (Option.some.inj same.1)
      subst owner
      rcases same.2 with rfl
      have store := store_word (hlc := hlc) capacity era g cpu unlockWrite 1#32 0#32 time
      dsimp only [unlockWrite, SpinlockAccess.writeRequest, SpinlockAccess.address] at store ⊢
      imod store $$ Hbundle Htso Hword with ⟨Hbundle, Htso, Hreceipt', Hword⟩
      imod Lock.release_at capacity.lock γ cpu oldPosition $$ Ha Hfrag with ⟨Ha, Hfrag⟩
      imodintro
      isplitl [Hword Ha Hfrag Hcounter]
      · unfold body
        iexists oldPosition
        iexists (g.log.length + 1)
        ileft
        iframe Hword Ha Hfrag
        iexists v
        iexists t
        iexact Hcounter
      · iframe Hbundle Htso
        iintro HpostView
        iexists Phase.idle
        isplit
        · ipureintro; exact WriteStep.release oldPosition v t
        · unfold payload; itrivial

end MachCSL.Logic.SpinlockProtocol
