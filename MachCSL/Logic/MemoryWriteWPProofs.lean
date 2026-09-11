import MachCSL.Logic.MemoryWriteWPState

namespace MachCSL.Logic.MemoryWriteWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

/-- The only additional pure callback fact comes from a proved native validity
bridge. Blocked writes retain the exact reservation and the unopened callback. -/
theorem wp_checked [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (contracts : Contracts capacity) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (rr : Option Reservation) (P : State → Prop) (post : Empty → IProp GF)
    (present : req.value = some value) (ram : deviceAddress req.pa = false)
    (guard : ∀ g, ThreadLive g gen →
      iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
        MachineInterp.generationCertificate capacity fixed gen era -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗ ⌜P g⌝)) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      checkedPremise capacity image fixed whole gen era cpu n req value k P post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold threadWP DeadThread.threadWP
  iintro #Hcert
  iloeb as IH
  iintro Hfrag Hwrite
  iapply wp_lift_step (s := .NotStuck) (E := ⊤) (Φ := post) (by rfl)
  iintro %g %ns %events %future %nt Hstate
  dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS]
  iunfold MachineInterp.stateInterp at Hstate
  ihave ⟨Hp, Ho⟩ := Hstate
  ihave %cases := MachineInterp.generation_cases capacity fixed g gen era $$ Hp Hcert
  rcases cases with older | live
  · ihave #Hdead := RegisterWP.power_dead capacity fixed g gen older $$ Hp
    have dead : ¬ ThreadLive g gen := by intro live; have := live.2; omega
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
    iintro Hback
    isplit
    · ipureintro
      exact ⟨[], _, g, [], DeadThread.dead_step image _ gen g rfl dead⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨rfl, rfl, rfl, rfl⟩ := DeadThread.dead_step_unique image _ gen g rfl dead events e' g' forks step
      imod Hback
      imodintro
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · have tail := DeadThread.wp_dead capacity image fixed whole
          (.hart gen cpu (.impure (.writeMem n req) k)) gen post rfl
        unfold DeadThread.threadWP at tail
        iapply tail $$ Hdead
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
  · classical
    by_cases free : Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu)
    · ihave %fact := guard g live $$ Hp Hcert Hfrag
      ihave ⟨Hera, HclosePower⟩ := power_write_access capacity fixed g gen era cpu req value live $$ Hp Hcert
      ihave ⟨Hbundle, Htso, HcloseEra⟩ := bundle_write_access capacity contracts.views contracts.reservations
        era g cpu req value free $$ Hera
      iunfold checkedPremise at Hwrite
      imod Hwrite $$ %g [] Hbundle Htso with Hclose
      · ipureintro; exact fact
      imodintro
      isplit
      · ipureintro
        exact ⟨[], _, writeState g cpu req value, [],
          written_step image g gen cpu n req value k present ram live free⟩
      · iintro !> %e' %g' %forks %step _
        rcases step_inv image g gen cpu n req value k present ram live events e' g' forks step with
          blocked | ⟨_, rfl, rfl, rfl, rfl⟩
        · exact False.elim (blocked.1 free)
        · imod Hclose with ⟨Hbundle, Htso, Hcontinue⟩
          imod HcloseEra $$ %rr Hbundle Htso Hfrag with ⟨Hera, Hfrag, Hreceipt⟩
          ihave Hp := HclosePower $$ Hera
          simp only [List.nil_append]
          ihave Ho := PowerGhost.obs_interp_silent capacity.power image _ _ g _ []
            (written_step image g gen cpu n req value k present ram live free)
            fixed.observations whole future $$ Ho
          imodintro
          simp only [List.length_nil, Nat.add_zero]
          dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
          iframe Hp Ho
          isplit
          · iunfold threadWP at Hcontinue
            iunfold DeadThread.threadWP at Hcontinue
            iapply Hcontinue $$ Hfrag Hreceipt
          · iapply BigSepL.bigSepL_nil.mpr
            itrivial
    · iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
      iintro Hback
      isplit
      · ipureintro
        exact ⟨[], _, g, [], blocked_step image g gen cpu n req value k present ram live free⟩
      · iintro !> %e' %g' %forks %step _
        rcases step_inv image g gen cpu n req value k present ram live events e' g' forks step with
          ⟨_, rfl, rfl, rfl, rfl⟩ | success
        · imod Hback
          imodintro
          simp only [List.nil_append, List.length_nil, Nat.add_zero]
          dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
          iframe Hp Ho
          isplit
          · iapply IH $$ Hfrag Hwrite
          · iapply BigSepL.bigSepL_nil.mpr
            itrivial
        · exact False.elim (free success.1)

theorem wp_write [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (contracts : Contracts capacity) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (rr : Option Reservation) (post : Empty → IProp GF)
    (present : req.value = some value) (ram : deviceAddress req.pa = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      writePremise capacity image fixed whole gen era cpu n req value k post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post) := by
  apply wp_checked capacity contracts image fixed whole gen era cpu n req value k rr (fun _ => True) post present ram
  intro g _
  iintro _ _ _
  ipureintro
  trivial

theorem wp_conditional [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (contracts : Contracts capacity) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (old value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (post : Empty → IProp GF) (present : req.value = some value)
    (ram : deviceAddress req.pa = false) (bound : n < 2 ^ 64) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot req.pa n old)) -∗
      conditionalPremise capacity image fixed whole gen era cpu n req old value k post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post) := by
  apply wp_checked capacity contracts image fixed whole gen era cpu n req value k
    (some (snapshot req.pa n old)) (fun g => readBytes g.memory req.pa n = some old) post present ram
  intro g live
  exact contracts.exclusive.heldSnapshot fixed g gen era cpu req.pa n old live bound

/-- The concrete ledger update pays the source callback's entire write change. -/
theorem bundle_store [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (contracts : Contracts capacity) (era : Era.Record) (g : State) (cpu : CPU)
    (n : Nat) (req : WriteRequest n) (old value : BitVec (8 * n)) (bound : n ≤ 2 ^ 64) :
    iprop(⊢ writeBundle capacity.era era g -∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g -∗
      TsoStore.ledgerWindow (storeCapacity capacity) (storeNames era) req.pa n old ==∗
      writeBundle capacity.era era (writeState g cpu req value) ∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (writeState g cpu req value) ∗
      Tso.History.logElem capacity.era.history era.logEntries g.log.length
        ⟨snapshot req.pa n value, hartAgent cpu⟩ ∗
      TsoStore.storedWindow (storeCapacity capacity) (storeNames era) req.pa n value (g.log.length + 1)) := by
  have validity : iprop(Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g ⊢ ⌜MemoryOK g⌝) := by
    unfold Tso.Interp.tsoInterpAt
    iintro ⟨%timestamps, %entries, _, _, _, _, _, _, _, %ok⟩
    ipureintro
    exact ok.1
  iintro Hbundle Htso Hledger
  ihave %ok := validity $$ Htso
  iunfold writeBundle at Hbundle
  iunfold MemoryExclusiveWP.readBundle at Hbundle
  icases Hbundle with ⟨Hr, Hheap, Hd⟩
  have store : iprop(⊢ Era.heapInterpAt capacity.era era g -∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g -∗
      TsoStore.ledgerWindow (storeCapacity capacity) (storeNames era) req.pa n old ==∗
      Era.heapInterpAt capacity.era era (writeState g cpu req value) ∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (writeState g cpu req value) ∗
      Tso.History.logElem capacity.era.history era.logEntries g.log.length
        ⟨snapshot req.pa n value, hartAgent cpu⟩ ∗
      TsoStore.storedWindow (storeCapacity capacity) (storeNames era) req.pa n value (g.log.length + 1)) :=
    contracts.store.window (storeNames era) era.imageBytes g (writeState g cpu req value)
      req.pa n old value (hartAgent cpu) bound (writeState_transition g cpu req value ok)
  imod store $$ Hheap Htso Hledger with ⟨Hheap, Htso, Hreceipt, Hledger⟩
  imodintro
  iframe Htso Hreceipt Hledger
  unfold writeBundle MemoryExclusiveWP.readBundle
  dsimp only [writeState]
  iframe

/-- Extraction/restoration of full ledger resources discharges the update
callback; the caller never supplies a write WP or a successor-preservation oracle. -/
theorem ledger_premise [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (contracts : Contracts capacity) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (P : State → Prop) (post : Empty → IProp GF) (bound : n ≤ 2 ^ 64) :
    iprop(ledgerPremise capacity image fixed whole gen era cpu n req value k P post ⊢
      checkedPremise capacity image fixed whole gen era cpu n req value k P post) := by
  unfold ledgerPremise checkedPremise
  iintro Haccess %g %fact Hbundle Htso
  imod Haccess $$ %g [] Hbundle Htso with Haccess
  · ipureintro; exact fact
  imodintro
  inext
  icases Haccess with ⟨%old, Hbundle, Htso, Hledger, Hclose⟩
  imod bundle_store capacity contracts era g cpu n req old value bound $$ Hbundle Htso Hledger with
    ⟨Hbundle, Htso, Hreceipt, Hledger⟩
  imod Hclose $$ Hledger Hreceipt with Hcontinue
  imodintro
  iframe

theorem wp_ledger [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (contracts : Contracts capacity) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (rr : Option Reservation) (post : Empty → IProp GF)
    (present : req.value = some value) (ram : deviceAddress req.pa = false) (bound : n ≤ 2 ^ 64) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ledgerPremise capacity image fixed whole gen era cpu n req value k (fun _ => True) post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post) := by
  iintro Hcert Hfrag Hledger
  ihave Hwrite := ledger_premise capacity contracts image fixed whole gen era cpu n req value k
    (fun _ => True) post bound $$ Hledger
  have rule := wp_write capacity contracts image fixed whole gen era cpu n req value k rr post present ram
  unfold writePremise at rule
  iapply rule $$ Hcert Hfrag Hwrite

theorem wp_conditional_ledger [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (contracts : Contracts capacity) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : WriteRequest n) (old value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (post : Empty → IProp GF) (present : req.value = some value)
    (ram : deviceAddress req.pa = false) (bound : n < 2 ^ 64) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot req.pa n old)) -∗
      ledgerPremise capacity image fixed whole gen era cpu n req value k
        (fun g => readBytes g.memory req.pa n = some old) post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post) := by
  iintro Hcert Hfrag Hledger
  ihave Hwrite := ledger_premise capacity contracts image fixed whole gen era cpu n req value k
    (fun g => readBytes g.memory req.pa n = some old) post (Nat.le_of_lt bound) $$ Hledger
  have rule := wp_conditional capacity contracts image fixed whole gen era cpu n req old value k post present ram bound
  unfold conditionalPremise at rule
  iapply rule $$ Hcert Hfrag Hwrite

theorem memoryWriteWPSpec [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (contracts : Contracts capacity) : MemoryWriteWPSpec capacity where
  write := wp_write capacity contracts
  conditional := wp_conditional capacity contracts
  ledger := wp_ledger capacity contracts
  conditionalLedger := wp_conditional_ledger capacity contracts

end MachCSL.Logic.MemoryWriteWP
