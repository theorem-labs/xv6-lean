import MachCSL.Logic.MemoryExclusiveWPSpec
import MachCSL.Logic.MemoryReadWPProofs
import MachCSL.Logic.RestartWPProofs
import MachCSL.Memory.ReservationProofs
import MachCSL.Logic.TsoStoreProofs

namespace MachCSL.Logic.MemoryExclusiveWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Memory MachCSL.Machine

theorem reserve_ok (g : State) (cpu : CPU) (value : Option Reservation)
    (ok : ReservationsOK g) (valid : ∀ r, value = some r → Submap r g.memory) :
    ReservationsOK (reserve g cpu value) := by
  intro other r present
  change updateHart g.reservations cpu value other = some r at present
  by_cases same : other = cpu
  · simp only [updateHart, if_pos same] at present
    exact valid r present
  · simp only [updateHart, if_neg same] at present
    exact ok other r present

theorem acquired_ok (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) (ok : ReservationsOK g) (reads : readBytes g.memory a n = some word) :
    ReservationsOK (acquired g cpu a n word) := by
  apply reserve_ok _ _ _ ok
  intro r same
  cases Option.some.inj same
  exact snapshot_submap g.memory a n word (readBytes_spec g.memory a n word reads)

theorem writeBack_acquired (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) :
    writeBack g cpu {focus g cpu with view := g.log.length, reservation := some (snapshot a n word)} =
      acquired g cpu a n word := by
  have same {α : Type} (f : CPU → α) : updateHart f cpu (f cpu) = f := by
    funext other
    by_cases h : other = cpu <;> simp [updateHart, h]
  simp only [writeBack, focus, acquired, reserve, TsoRead.advanceView, same]

theorem acquired_view (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat) (word : BitVec (8 * n)) :
    (acquired g cpu a n word).views cpu = g.log.length := by
  simp [acquired, reserve, TsoRead.advanceView, updateHart]

theorem acquired_reservation (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) :
    (acquired g cpu a n word).reservations cpu = some (snapshot a n word) := by
  simp [acquired, reserve, updateHart]

theorem acquired_frame (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat) (word : BitVec (8 * n)) :
    (acquired g cpu a n word).registers = g.registers ∧
    (acquired g cpu a n word).memory = g.memory ∧
    (acquired g cpu a n word).devices = g.devices ∧
    (acquired g cpu a n word).generation = g.generation ∧
    (acquired g cpu a n word).power = g.power ∧
    (acquired g cpu a n word).image = g.image ∧
    (acquired g cpu a n word).log = g.log ∧
    (∀ other, other ≠ cpu → (acquired g cpu a n word).views other = g.views other ∧
      (acquired g cpu a n word).reservations other = g.reservations other) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro other different
  simp [acquired, reserve, TsoRead.advanceView, updateHart, different]

/-- The current physical-memory read is exactly a TSO read at the log top,
using the actual interpretation's flat-memory equality. -/
theorem read_current_top (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) (ok : MemoryOK g) (reads : readBytes g.memory a n = some word) :
    ReadsBytes g.image g.log (hartAgent cpu) g.log.length a n word := by
  intro j hj
  rw [read_top_flat, ← ok.1]
  exact readBytes_spec g.memory a n word reads j hj

theorem blocked_step [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (n : Nat) (req : ReadRequest n) (k : ReadResult n → SailM Unit)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true)
    (live : ThreadLive g gen) (blocked : ¬ Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu)) :
    Step image (.hart gen cpu (.impure (.readMem n req) k)) g []
      (.hart gen cpu (.impure (.readMem n req) k)) (RestartWP.clearReservation g cpu) [] := by
  apply Step.hartLive _ _ _ _ _ _ live
  refine ⟨{focus g cpu with reservation := none}, ?_, (RestartWP.writeBack_clear g cpu).symm⟩
  simp only [NodeStep, ram, Bool.false_eq_true, ↓reduceIte]
  exact Or.inr ⟨exclusive, Or.inl ⟨blocked, True.intro, True.intro⟩⟩

theorem acquired_step [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (n : Nat) (req : ReadRequest n) (k : ReadResult n → SailM Unit)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true)
    (live : ThreadLive g gen) (free : Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu))
    (word : BitVec (8 * n)) (reads : readBytes g.memory req.pa n = some word) :
    Step image (.hart gen cpu (.impure (.readMem n req) k)) g []
      (.hart gen cpu (k (.Ok (word, none)))) (acquired g cpu req.pa n word) [] := by
  apply Step.hartLive _ _ _ _ _ _ live
  refine ⟨{focus g cpu with view := g.log.length, reservation := some (snapshot req.pa n word)},
    ?_, (writeBack_acquired g cpu req.pa n word).symm⟩
  simp only [NodeStep, ram, Bool.false_eq_true, ↓reduceIte]
  exact Or.inr ⟨exclusive, Or.inr ⟨free, word, readBytes_spec g.memory req.pa n word reads, rfl, rfl⟩⟩

theorem step_inv [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (n : Nat) (req : ReadRequest n) (k : ReadResult n → SailM Unit)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true)
    (live : ThreadLive g gen) (events : List Observation) (e' : Expr) (g' : State) (forks : List Expr)
    (step : Step image (.hart gen cpu (.impure (.readMem n req) k)) g events e' g' forks) :
    (¬ Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu) ∧
      e' = .hart gen cpu (.impure (.readMem n req) k) ∧ g' = RestartWP.clearReservation g cpu ∧
      forks = [] ∧ events = []) ∨
    (Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu) ∧
      ∃ word, readBytes g.memory req.pa n = some word ∧ e' = .hart gen cpu (k (.Ok (word, none))) ∧
        g' = acquired g cpu req.pa n word ∧ forks = [] ∧ events = []) := by
  cases step with
  | hartDead _ _ _ _ dead => exact False.elim (dead live)
  | hartLive _ _ _ m' _ _ _ h =>
    obtain ⟨after, node, hg⟩ := h
    simp only [NodeStep, ram, exclusive, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, true_and, false_and, false_or] at node
    rcases node with ⟨blocked, hm, hs⟩ | ⟨free, word, reads, hm, hs⟩
    · subst after; subst m'
      exact Or.inl ⟨blocked, rfl, hg.trans (RestartWP.writeBack_clear g cpu), rfl, rfl⟩
    · subst after; subst m'
      exact Or.inr ⟨free, word, readBytes_of_bytes g.memory req.pa n word reads,
        rfl, hg.trans (writeBack_acquired g cpu req.pa n word), rfl, rfl⟩

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

theorem era_reserve (era : Era.Record) (g : State) (cpu : CPU) (old value : Option Reservation)
    (valid : ∀ r, value = some r → Submap r g.memory) :
    iprop(⊢ Era.interp capacity.era era g -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu old ==∗
      Era.interp capacity.era era (reserve g cpu value) ∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu value) := by
  unfold Era.interp
  iintro ⟨Hregs, Hheap, Hdev, Hdisk, Htso, Hresv, %ok⟩ Hfrag
  imod Reservations.resvFrag_update capacity.era.reservations era.reservations g.reservations cpu old value
    $$ Hresv Hfrag with ⟨Hresv, Hfrag⟩
  imodintro
  have heap : Era.heapInterpAt capacity.era era (reserve g cpu value) = Era.heapInterpAt capacity.era era g := rfl
  have tso : Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (reserve g cpu value) =
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g := rfl
  rw [heap, tso]
  unfold reserve
  iframe
  ipureintro
  exact reserve_ok g cpu value ok valid

theorem power_reserve (fixed : MachineInterp.FixedNames) (g : State) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (old value : Option Reservation) (live : ThreadLive g gen)
    (valid : ∀ r, value = some r → Submap r g.memory) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu old ==∗
      MachineInterp.powerInterp capacity fixed (reserve g cpu value) ∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu value) :=
  MachineInterp.live_update capacity fixed g (reserve g cpu value) gen era live rfl rfl rfl _ _
    (era_reserve capacity era g cpu old value valid)

theorem bundle_access (era : Era.Record) (g : State) :
    iprop(⊢ Era.interp capacity.era era g -∗ readBundle capacity.era era g ∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g ∗
      (readBundle capacity.era era g -∗
        Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g -∗
        Era.interp capacity.era era g)) := by
  unfold Era.interp readBundle
  iintro ⟨Hr, Hheap, Hd, Hdisk, Htso, Hresv, Hok⟩
  iframe Hr Hheap Hd Htso
  iintro ⟨Hr, Hheap, Hd⟩ Htso
  iframe

theorem bundle_advance (era : Era.Record) (g : State) (cpu : CPU) (view : Nat) :
    readBundle capacity.era era (TsoRead.advanceView g cpu view) = readBundle capacity.era era g := rfl

theorem held_submap (fixed : MachineInterp.FixedNames) (g : State) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (r : Reservation) (live : ThreadLive g gen) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some r) -∗
      ⌜Submap r g.memory⌝) := by
  iintro Hp Hcert Hfrag
  ihave ⟨Hera, _⟩ := MachineInterp.live_era_access capacity fixed g gen era live $$ Hp Hcert
  iunfold Era.interp at Hera
  ihave ⟨_, _, _, _, _, Hresv, %ok⟩ := Hera
  ihave %same := Reservations.resvFrag_agree capacity.era.reservations era.reservations g.reservations cpu
    (some r) $$ Hresv Hfrag
  ipureintro
  exact ok cpu r same

theorem heap_window_read (era : Era.Record) (g : State) (a : PhysicalAddress) (n : Nat)
    (dq : DFrac) (word : BitVec (8 * n)) :
    iprop(⊢ Era.heapInterpAt capacity.era era g -∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap a n dq word -∗
      ⌜readBytes g.memory a n = some word⌝) := by
  unfold Era.heapInterpAt TsoRead.byteWindow
  iintro ⟨%memory, Hheap, %rep⟩ Hbytes
  iapply pure_mono (fun h => readBytes_of_bytes g.memory a n word h)
  iapply pure_forall.mpr
  iintro %j
  iapply pure_imp.mpr
  iintro %bound
  have present : (List.range n)[j]? = some j := by simp [bound]
  ihave ⟨Hbyte, _⟩ := BigSepL.bigSepL_lookup present $$ Hbytes
  have valid := Heap.valid capacity.era.heap ⟨era.heap, era.metadata⟩ memory (addressAdd a j) dq (nthByte word j)
  rw [Heap.pointsto_eq_byteElem] at valid
  ihave %lookup := valid $$ Hheap Hbyte
  ipureintro
  rw [← rep]
  exact lookup

/-- Source snap_of_read_bytes. The strict source width bound rules out
repeated addresses within the modular window, without an alignment premise. -/
theorem snapshot_read (memory : ByteMap 64) (a : PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) (bound : n < 2 ^ 64) (sub : Submap (snapshot a n word) memory) :
    readBytes memory a n = some word := by
  apply readBytes_of_bytes
  intro j hj
  apply sub
  rw [← TsoStore.windowMap_decode]
  change PartialMap.get? (TsoStore.windowMap a n word) (addressAdd a j) = some (nthByte word j)
  unfold TsoStore.windowMap
  exact LawfulPartialMap.get?_ofList_some
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    (TsoStore.windowEntries_nodup a n word (Nat.le_of_lt bound))

theorem held_snapshot_read (fixed : MachineInterp.FixedNames) (g : State) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (a : PhysicalAddress) (n : Nat) (word : BitVec (8 * n))
    (live : ThreadLive g gen) (bound : n < 2 ^ 64) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot a n word)) -∗
      ⌜readBytes g.memory a n = some word⌝) := by
  iintro Hp Hcert Hfrag
  ihave %sub := held_submap capacity fixed g gen era cpu (snapshot a n word) live $$ Hp Hcert Hfrag
  ipureintro
  exact snapshot_read g.memory a n word bound sub

/-- The retry induction keeps an existential reservation fragment because the
blocked arm replaces any old snapshot with none. The public rule below exposes
the exact source fragment parameter. -/
private theorem wp_exclusive_any [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (post : Empty → IProp GF)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvAny capacity.era.reservations era.reservations cpu -∗
      exclusivePremise capacity image fixed whole gen era cpu n req k post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  letI := language image
  letI := MachineInterp.irisGS capacity image fixed whole
  unfold threadWP DeadThread.threadWP
  iintro #Hcert
  iloeb as IH
  iintro Hany Hread
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
          (.hart gen cpu (.impure (.readMem n req) k)) gen post rfl
        unfold DeadThread.threadWP at tail
        iapply tail $$ Hdead
      · iapply BigSepL.bigSepL_nil.mpr
        itrivial
  · classical
    by_cases free : Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu)
    · ihave %ok := TsoRead.power_memoryOK capacity fixed g gen era live $$ Hp Hcert
      imod TsoRead.power_advance capacity fixed g gen era cpu g.log.length live (ok.2.1 cpu)
        (Nat.le_refl _) $$ Hp Hcert with ⟨Hp, Hreceipt⟩
      ihave ⟨Hera, HclosePower⟩ := MachineInterp.live_era_access capacity fixed
        (TsoRead.advanceView g cpu g.log.length) gen era live $$ Hp Hcert
      ihave ⟨Hbundle, Htso, HcloseEra⟩ := bundle_access capacity era
        (TsoRead.advanceView g cpu g.log.length) $$ Hera
      rw [bundle_advance]
      iunfold exclusivePremise at Hread
      imod Hread $$ %g Hbundle Htso Hreceipt with ⟨%word, %reads, Hclose⟩
      imodintro
      isplit
      · ipureintro
        exact ⟨[], _, acquired g cpu req.pa n word, [],
          acquired_step image g gen cpu n req k ram exclusive live free word reads⟩
      · iintro !> %e' %g' %forks %step _
        rcases step_inv image g gen cpu n req k ram exclusive live events e' g' forks step with
          blocked | ⟨_, word', reads', rfl, rfl, rfl, rfl⟩
        · exact False.elim (blocked.1 free)
        · have same : word' = word := Option.some.inj (reads'.symm.trans reads)
          subst word'
          imod Hclose with ⟨Hbundle, Htso, Hcontinue⟩
          ihave Hera := HcloseEra $$ Hbundle Htso
          ihave Hp := HclosePower $$ Hera
          iunfold Reservations.resvAny at Hany
          ihave ⟨%rr, Hfrag⟩ := Hany
          have valid : ∀ r, some (snapshot req.pa n word) = some r → Submap r g.memory := by
            intro r same
            cases Option.some.inj same
            exact snapshot_submap g.memory req.pa n word (readBytes_spec g.memory req.pa n word reads)
          imod power_reserve capacity fixed (TsoRead.advanceView g cpu g.log.length) gen era cpu rr
            (some (snapshot req.pa n word)) live valid $$ Hp Hcert Hfrag with ⟨Hp, Hfrag⟩
          rw [← acquired]
          simp only [List.nil_append]
          ihave Ho := PowerGhost.obs_interp_silent capacity.power image _ _ g _ []
            (acquired_step image g gen cpu n req k ram exclusive live free word reads)
            fixed.observations whole future $$ Ho
          imodintro
          simp only [List.length_nil, Nat.add_zero]
          dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
          iframe Hp Ho
          isplit
          · iunfold threadWP at Hcontinue
            iunfold DeadThread.threadWP at Hcontinue
            iapply Hcontinue $$ Hfrag
          · iapply BigSepL.bigSepL_nil.mpr
            itrivial
    · iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
      iintro Hback
      isplit
      · ipureintro
        exact ⟨[], _, RestartWP.clearReservation g cpu, [], blocked_step image g gen cpu n req k ram exclusive live free⟩
      · iintro !> %e' %g' %forks %step _
        rcases step_inv image g gen cpu n req k ram exclusive live events e' g' forks step with
          ⟨_, rfl, rfl, rfl, rfl⟩ | success
        · imod RestartWP.power_clear capacity fixed g gen era cpu live $$ Hp Hcert Hany with ⟨Hp, Hnone⟩
          ihave Hany := Reservations.resvAny_intro capacity.era.reservations era.reservations cpu none $$ Hnone
          simp only [List.nil_append]
          ihave Ho := PowerGhost.obs_interp_silent capacity.power image _ _ g _ []
            (blocked_step image g gen cpu n req k ram exclusive live free)
            fixed.observations whole future $$ Ho
          imod Hback
          imodintro
          simp only [List.length_nil, Nat.add_zero]
          dsimp only [Iris.StateInterp.stateInterp, MachineInterp.irisGS, MachineInterp.stateInterp]
          iframe Hp Ho
          isplit
          · iapply IH $$ Hany Hread
          · iapply BigSepL.bigSepL_nil.mpr
            itrivial
        · exact False.elim (free success.1)

theorem wp_exclusive [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (rr : Option Reservation) (post : Empty → IProp GF)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      exclusivePremise capacity image fixed whole gen era cpu n req k post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  iintro Hcert Hfrag Hread
  ihave Hany := Reservations.resvAny_intro capacity.era.reservations era.reservations cpu rr $$ Hfrag
  iapply wp_exclusive_any capacity image fixed whole gen era cpu n req k post ram exclusive $$ Hcert Hany Hread

theorem wp_bytes [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (rr : Option Reservation) (dq : DFrac)
    (word : BitVec (8 * n)) (post : Empty → IProp GF)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
      ▷ (∀ view, TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot req.pa n word)) -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  iintro Hcert Hfrag Hbytes Hcontinue
  iapply wp_exclusive capacity image fixed whole gen era cpu n req k rr post ram exclusive $$ Hcert Hfrag
  unfold exclusivePremise
  iintro %g Hbundle Htso Hreceipt
  iunfold readBundle at Hbundle
  ihave ⟨Hr, Hheap, Hd⟩ := Hbundle
  ihave %reads := heap_window_read capacity era g req.pa n dq word $$ Hheap Hbytes
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  iexists word
  isplit
  · ipureintro; exact reads
  · iintro !>
    imod Hback
    imodintro
    unfold readBundle
    iframe Hr Hheap Hd Htso
    iintro Hfrag
    iapply Hcontinue $$ %g.log.length Hbytes Hfrag Hreceipt

theorem memoryExclusiveWPSpec [Platform] {hlc : HasLC} [InvGS_gen hlc GF] :
    MemoryExclusiveWPSpec capacity :=
  ⟨held_submap capacity, held_snapshot_read capacity, wp_exclusive capacity, wp_bytes capacity⟩

end MachCSL.Logic.MemoryExclusiveWP
