import MachCSL.Logic.MemoryReadWPSpec
import MachCSL.Logic.TsoReadLink
import MachCSL.Logic.RegisterWPProofs

namespace MachCSL.Logic.MemoryReadWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Memory MachCSL.Machine

theorem readsBytes_unique {image : ByteMap width} {log : WriteLog width} {h view : Nat}
    {a : Address width} {n : Nat} {left right : BitVec (8 * n)}
    (hl : ReadsBytes image log h view a n left) (hr : ReadsBytes image log h view a n right) : left = right := by
  apply bv_eq_of_bytes
  intro j hj
  exact Option.some.inj ((hl j hj).symm.trans (hr j hj))

theorem plain_step [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (n : Nat) (req : ReadRequest n) (k : ReadResult n → SailM Unit)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    (live : ThreadLive g gen) (view : Nat) (word : BitVec (8 * n))
    (lower : g.views cpu ≤ view) (upper : view ≤ g.log.length)
    (reads : ReadsBytes g.image g.log (hartAgent cpu) view req.pa n word) :
    Step image (.hart gen cpu (.impure (.readMem n req) k)) g []
      (.hart gen cpu (k (.Ok (word, none)))) (TsoRead.advanceView g cpu view) [] := by
  apply Step.hartLive _ _ _ _ _ _ live
  refine ⟨{ focus g cpu with view := view }, ?_, (TsoRead.writeBack_view g cpu view).symm⟩
  simp only [NodeStep, ram, Bool.false_eq_true, ↓reduceIte]
  exact Or.inl ⟨plain, view, word, lower, upper, reads, rfl, rfl⟩

theorem plain_step_inv [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (n : Nat) (req : ReadRequest n) (k : ReadResult n → SailM Unit)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    (live : ThreadLive g gen) (events : List Observation) (e' : Expr) (g' : State) (forks : List Expr)
    (step : Step image (.hart gen cpu (.impure (.readMem n req) k)) g events e' g' forks) :
    ∃ view word, g.views cpu ≤ view ∧ view ≤ g.log.length ∧
      ReadsBytes g.image g.log (hartAgent cpu) view req.pa n word ∧
      e' = .hart gen cpu (k (.Ok (word, none))) ∧ g' = TsoRead.advanceView g cpu view ∧
      forks = [] ∧ events = [] := by
  cases step with
  | hartDead _ _ _ _ dead => exact False.elim (dead live)
  | hartLive _ _ _ m' _ _ _ h =>
    obtain ⟨after, node, hg⟩ := h
    simp only [NodeStep, ram, plain, Bool.false_eq_true, ↓reduceIte, true_and, false_and, or_false] at node
    obtain ⟨view, word, lower, upper, reads, hm, hs⟩ := node
    subst after
    subst m'
    exact ⟨view, word, lower, upper, reads, rfl, hg.trans (TsoRead.writeBack_view g cpu view), rfl, rfl⟩


variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

theorem wp_ram_read_plain_ex [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (P : BitVec (8 * n) → Prop) (post : Empty → IProp GF)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      plainPremise capacity image fixed whole gen era cpu n req k P post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold threadWP DeadThread.threadWP
  iintro #Hcert Hread
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
      · have tail := DeadThread.wp_dead capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) gen post rfl
        unfold DeadThread.threadWP at tail
        iapply tail $$ Hdead
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
  · ihave %ok := TsoRead.power_memoryOK capacity fixed g gen era live $$ Hp Hcert
    iunfold plainPremise at Hread
    imod Hread $$ [] Hp with ⟨%readable, Hclose⟩
    · ipureintro; exact live
    obtain ⟨word, reads, _⟩ := readable (g.views cpu) (Nat.le_refl _) (ok.2.1 cpu)
    imodintro
    isplit
    · ipureintro
      exact ⟨[], _, TsoRead.advanceView g cpu (g.views cpu), [],
        plain_step image g gen cpu n req k ram plain live (g.views cpu) word (Nat.le_refl _) (ok.2.1 cpu) reads⟩
    · iintro !> %e' %g' %forks %step _
      obtain ⟨view, word', lower, upper, actual, rfl, rfl, rfl, rfl⟩ :=
        plain_step_inv image g gen cpu n req k ram plain live events e' g' forks step
      obtain ⟨good, goodRead, property⟩ := readable view lower upper
      have same : word' = good := readsBytes_unique actual goodRead
      subst good
      imod Hclose with ⟨Hp, Hcontinue⟩
      imod TsoRead.power_advance capacity fixed g gen era cpu view live lower upper $$ Hp Hcert with ⟨Hp, Hreceipt⟩
      simp only [List.nil_append]
      ihave Ho := PowerGhost.obs_interp_silent capacity.power image _ _ g _ []
        (plain_step image g gen cpu n req k ram plain live view word' lower upper actual)
        fixed.observations whole future $$ Ho
      imodintro
      simp only [List.length_nil, Nat.add_zero]
      dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
      iframe Hp Ho
      isplit
      · iunfold threadWP at Hcontinue
        iunfold DeadThread.threadWP at Hcontinue
        iapply Hcontinue $$ [] [] [] [] Hreceipt
        · ipureintro; exact lower
        · ipureintro; exact upper
        · ipureintro; exact actual
        · ipureintro; exact property
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial


theorem wp_ram_read_plain [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (post : Empty → IProp GF)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      plainWordPremise capacity image fixed whole gen era cpu n req k post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  iintro #Hcert Hread
  iapply wp_ram_read_plain_ex capacity image fixed whole gen era cpu n req k (fun _ => True) post ram plain $$ Hcert
  unfold plainPremise
  iintro %g %live Hp
  iunfold plainWordPremise at Hread
  imod Hread $$ [] Hp with ⟨%word, %readable, Hclose⟩
  · ipureintro; exact live
  imodintro
  isplit
  · ipureintro
    intro view lower upper
    exact ⟨word, readable view lower upper, True.intro⟩
  · iintro !>
    imod Hclose with ⟨Hp, Hcontinue⟩
    imodintro
    iframe Hp
    iintro %view %actual %lower %upper %reads _ Hreceipt
    have same : actual = word := readsBytes_unique reads (readable view lower upper)
    subst actual
    iapply Hcontinue $$ [] [] Hreceipt
    · ipureintro; exact lower
    · ipureintro; exact upper


theorem wp_ram_read_pristine [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (dq : DFrac) (word : BitVec (8 * n)) (post : Empty → IProp GF)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
      TsoRead.pristineWindow capacity.era.heap.ledger era.timestamps req.pa n -∗
      ▷ (∀ view, TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  iintro #Hcert Hbytes #Hpristine Hcontinue
  iapply wp_ram_read_plain_ex capacity image fixed whole gen era cpu n req k (fun value => value = word) post ram plain $$ Hcert
  unfold plainPremise
  iintro %g %live Hp
  ihave %reads := TsoRead.power_pristine_read capacity fixed g gen era live req.pa n dq word $$ Hp Hcert Hbytes Hpristine
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  isplit
  · ipureintro
    intro view _ _
    exact ⟨word, reads _ _, rfl⟩
  · iintro !>
    imod Hback
    imodintro
    iframe Hp
    iintro %view %value %lower %upper %read %same Hreceipt
    subst value
    iapply Hcontinue $$ Hbytes Hreceipt


/-- A concrete client can start with the actual writable timestamp-zero window;
its conversion to pristine ownership is paid here and returned explicitly. -/
theorem wp_ram_read_pristine_mint [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (dq : DFrac) (word : BitVec (8 * n)) (post : Empty → IProp GF)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
      TsoRead.initialTimestampWindow capacity.era.heap.ledger era.timestamps req.pa n -∗
      ▷ (∀ view, TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
        TsoRead.pristineWindow capacity.era.heap.ledger era.timestamps req.pa n -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold threadWP DeadThread.threadWP
  iintro Hcert Hbytes Htimestamps Hcontinue
  imod TsoRead.pristine_window_mint capacity.era.heap.ledger era.timestamps req.pa n $$ Htimestamps with #Hpristine
  have rule := wp_ram_read_pristine capacity image fixed whole gen era cpu n req k dq word post ram plain
  unfold threadWP DeadThread.threadWP at rule
  iapply rule $$ Hcert Hbytes Hpristine
  iintro !> %view Hbytes Hreceipt
  iapply Hcontinue $$ Hbytes Hpristine Hreceipt


theorem memoryReadWPSpec [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : MemoryReadWPSpec capacity :=
  ⟨wp_ram_read_plain_ex capacity, wp_ram_read_plain capacity, wp_ram_read_pristine capacity,
    wp_ram_read_pristine_mint capacity⟩

end MachCSL.Logic.MemoryReadWP
