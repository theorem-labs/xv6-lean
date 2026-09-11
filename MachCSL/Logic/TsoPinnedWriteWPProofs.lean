import MachCSL.Logic.TsoPinnedWriteWPSpec
import MachCSL.Logic.TsoPinnedStoreProofs
import MachCSL.Logic.MemoryWriteWPLink

namespace MachCSL.Logic.TsoPinnedWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- Modular offset recovery needs only the fixed window size, including when
its base crosses the end of the address space. -/
theorem offset_addressAdd (a : PhysicalAddress) (j : Nat) (h : j < 8) :
    (addressAdd a j - a).toNat = j := by
  simp only [addressAdd, BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem write_effect (g : State) (cpu : CPU) (req : MemoryWriteWP.WriteRequest 8)
    (word : BitVec 64) (exclusive : accessExclusive req.access_kind = true) :
    Effect g (MemoryWriteWP.writeState g cpu req word) cpu req word := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [MemoryWriteWP.writeState, MemoryWriteWP.postView, exclusive, ↓reduceIte]

theorem step_inv [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (req : MemoryWriteWP.WriteRequest 8) (word : BitVec 64)
    (k : MemoryWriteWP.WriteResult → SailM Unit) (present : req.value = some word)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true)
    (live : ThreadLive g gen) (events : List Observation) (next : Expr) (after : State)
    (forks : List Expr)
    (step : Step image (.hart gen cpu (.impure (.writeMem 8 req) k)) g events next after forks) :
    (¬Disjoint (Footprint req.pa 8) (othersReserved g.reservations cpu) ∧
      next = .hart gen cpu (.impure (.writeMem 8 req) k) ∧ after = g ∧ forks = [] ∧ events = []) ∨
    (Disjoint (Footprint req.pa 8) (othersReserved g.reservations cpu) ∧
      next = .hart gen cpu (k (.Ok none)) ∧ after = MemoryWriteWP.writeState g cpu req word ∧
      Effect g after cpu req word ∧ forks = [] ∧ events = []) := by
  rcases MemoryWriteWP.step_inv image g gen cpu 8 req word k present ram live
    events next after forks step with blocked | ⟨free, nextEq, stateEq, forkEq, eventEq⟩
  · exact Or.inl blocked
  · subst after
    exact Or.inr ⟨free, nextEq, rfl, write_effect g cpu req word exclusive, forkEq, eventEq⟩

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

/-- Only a projection for a pure validity query; callers frame the complete
pin window rather than splitting the same fraction into two resources. -/
theorem window_bytes (era : Era.Record) (a : PhysicalAddress) (word : BitVec 64)
    (dq : DFrac) (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) :
    iprop(pinWindow capacity era a word dq floors sets ⊢
      TsoRead.byteWindow capacity.era.heap.ledger era.heap a 8 dq word) := by
  unfold pinWindow TsoPinnedStore.pinWindow TsoRead.byteWindow
  unfold MemoryWriteWP.storeCapacity MemoryWriteWP.storeNames Era.Record.tsoNames
  apply BigSepL.bigSepL_mono
  intro i j _
  iintro ⟨%time, Hbyte, _⟩
  iexact Hbyte

theorem heap_word_read (era : Era.Record) (g : State) (a : PhysicalAddress)
    (word : BitVec 64) (dq : DFrac) (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) :
    iprop(⊢ Era.heapInterpAt capacity.era era g -∗
      pinWindow capacity era a word dq floors sets -∗ ⌜readBytes g.memory a 8 = some word⌝) := by
  iintro Hheap Hpin
  ihave Hbytes := window_bytes capacity era a word dq floors sets $$ Hpin
  iapply MemoryExclusiveWP.heap_window_read capacity era g a 8 dq word $$ Hheap Hbytes

/-- A retained snapshot and a newly opened full-state slot describe the same
current word. This says nothing about other CPUs' reservation disjointness. -/
theorem held_word_agreement (fixed : MachineInterp.FixedNames) (g : State) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (a : PhysicalAddress) (reserved physical : BitVec 64)
    (dq : DFrac) (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) (live : ThreadLive g gen) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot a 8 reserved)) -∗
      pinWindow capacity era a physical dq floors sets -∗ ⌜physical = reserved⌝) := by
  iintro Hp Hcert Hresv Hpin
  ihave %readReserved := MemoryExclusiveWP.held_snapshot_read capacity fixed g gen era cpu a 8 reserved
    live (by decide) $$ Hp Hcert Hresv
  ihave ⟨Hera, _⟩ := MachineInterp.live_era_access capacity fixed g gen era live $$ Hp Hcert
  iunfold Era.interp at Hera
  ihave ⟨_, Hheap, _, _, _, _, _⟩ := Hera
  ihave %readPhysical := heap_word_read capacity era g a physical dq floors sets $$ Hheap Hpin
  ipureintro
  exact Option.some.inj (readPhysical.symm.trans readReserved)

/-- The validity query consumes no client ownership in this framed form. -/
theorem held_word_agreement_preserve (fixed : MachineInterp.FixedNames) (g : State) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (a : PhysicalAddress) (reserved physical : BitVec 64)
    (dq : DFrac) (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) (live : ThreadLive g gen) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot a 8 reserved)) -∗
      pinWindow capacity era a physical dq floors sets -∗
      MachineInterp.powerInterp capacity fixed g ∗
      MachineInterp.generationCertificate capacity fixed gen era ∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot a 8 reserved)) ∗
      pinWindow capacity era a physical dq floors sets ∗ ⌜physical = reserved⌝) := by
  iintro Hp Hcert Hresv Hpin
  ihave %same := held_word_agreement capacity fixed g gen era cpu a reserved physical dq floors sets live
    $$ Hp Hcert Hresv Hpin
  iframe Hp Hcert Hresv Hpin
  ipureintro
  exact same

/-- Pay the pinned update with actual complete heap metadata and TSO. The
modular floor/set map is constructed internally, not supplied as an oracle. -/
theorem bundle_store (era : Era.Record) (g : State) (cpu : CPU)
    (req : MemoryWriteWP.WriteRequest 8) (old new : BitVec 64)
    (floors : Nat → Nat) (sets : Nat → Tso.ByteSet)
    (members : ∀ j, j < 8 → nthByte new j ∈ sets j) :
    iprop(⊢ MemoryWriteWP.writeBundle capacity.era era g -∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g -∗
      pinWindow capacity era req.pa old (.own 1) floors sets ==∗
      MemoryWriteWP.writeBundle capacity.era era (MemoryWriteWP.writeState g cpu req new) ∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (MemoryWriteWP.writeState g cpu req new) ∗
      Tso.History.logElem capacity.era.history era.logEntries g.log.length
        ⟨snapshot req.pa 8 new, hartAgent cpu⟩ ∗
      storedWindow capacity era req.pa new (g.log.length + 1) floors sets) := by
  have validity : iprop(Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g ⊢ ⌜MemoryOK g⌝) := by
    unfold Tso.Interp.tsoInterpAt
    iintro ⟨%timestamps, %entries, _, _, _, _, _, _, _, %ok⟩
    ipureintro
    exact ok.1
  iintro Hbundle Htso Hpin
  ihave %ok := validity $$ Htso
  iunfold MemoryWriteWP.writeBundle at Hbundle
  iunfold MemoryExclusiveWP.readBundle at Hbundle
  icases Hbundle with ⟨Hregs, Hheap, Hdevice⟩
  have store : iprop(⊢ Era.heapInterpAt capacity.era era g -∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g -∗
      pinWindow capacity era req.pa old (.own 1) floors sets ==∗
      Era.heapInterpAt capacity.era era (MemoryWriteWP.writeState g cpu req new) ∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (MemoryWriteWP.writeState g cpu req new) ∗
      Tso.History.logElem capacity.era.history era.logEntries g.log.length
        ⟨snapshot req.pa 8 new, hartAgent cpu⟩ ∗
      storedWindow capacity era req.pa new (g.log.length + 1) floors sets) :=
    (TsoPinnedStore.storeSpec (MemoryWriteWP.storeCapacity capacity)
      (TsoStore.nativeContracts (MemoryWriteWP.storeCapacity capacity))).window
    (MemoryWriteWP.storeNames era) era.imageBytes g (MemoryWriteWP.writeState g cpu req new)
    req.pa 8 old new (hartAgent cpu) floors sets
    (fun a => floors (BitVec.sub a req.pa).toNat) (fun a => sets (BitVec.sub a req.pa).toNat)
    (by decide) (fun j hj => congrArg floors (offset_addressAdd req.pa j hj))
    (fun j hj => congrArg sets (offset_addressAdd req.pa j hj)) members
    (MemoryWriteWP.writeState_transition g cpu req new ok)
  imod store $$ Hheap Htso Hpin with ⟨Hheap, Htso, Hreceipt, Hpin⟩
  imodintro
  iframe Htso Hreceipt Hpin
  unfold MemoryWriteWP.writeBundle MemoryExclusiveWP.readBundle
  dsimp only [MemoryWriteWP.writeState]
  iframe Hregs Hheap Hdevice

/-- The conditional rule supplies real held-snapshot readback internally.
The pinned update runs only in the successful event's later; blocked writes
retain both the old snapshot fragment and the complete resource payer. -/
theorem wp_write [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    image fixed whole gen era cpu (req : MemoryWriteWP.WriteRequest 8)
    (reserved physical new : BitVec 64) floors sets (k : MemoryWriteWP.WriteResult → SailM Unit) post
    (present : req.value = some new) (ram : deviceAddress req.pa = false)
    (exclusive : accessExclusive req.access_kind = true)
    (members : ∀ j, j < 8 → nthByte new j ∈ sets j) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot req.pa 8 reserved)) -∗
      pinWindow capacity era req.pa physical (.own 1) floors sets -∗
      continuation capacity image fixed whole gen era cpu req.pa new floors sets (k (.Ok none)) post -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.writeMem 8 req) k)) post) := by
  iintro Hcert Hresv Hpin Hcontinue
  iunfold continuation at Hcontinue
  iapply MemoryWriteWP.wp_conditional capacity (MemoryWriteWP.nativeContracts capacity)
    image fixed whole gen era cpu 8 req reserved new k post present ram (by decide) $$ Hcert Hresv
  unfold MemoryWriteWP.conditionalPremise MemoryWriteWP.checkedPremise
  iintro %g %readReserved Hbundle Htso
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  iintro !>
  imod bundle_store capacity era g cpu req physical new floors sets members $$ Hbundle Htso Hpin
    with ⟨Hbundle, Htso, Hreceipt, Hpin⟩
  imod Hback
  imodintro
  iframe Hbundle Htso
  iintro Hresv Hview
  iapply Hcontinue $$ %(g.log.length + 1) Hpin [Hreceipt] [] Hresv
  · simp only [Nat.add_sub_cancel]
    iexact Hreceipt
  · ipureintro; omega
  · have same : MemoryWriteWP.postView g cpu req = g.log.length + 1 := by
      simp only [MemoryWriteWP.postView, exclusive, ↓reduceIte]
    rw [← same]
    iexact Hview

/-- Exact builtin equation includes both raw response arms. Only the live RAM
step inversion rules out a completed error response in the native WP. -/
theorem write_ram_eq [Platform] (a : PhysicalAddress) (word : BitVec 64) :
    LeanPaperStock.Functions.write_ram .Write_RISCV_conditional (.Physaddr a) 8 word () =
      (.impure (.writeMem 8 (conditionalRequest a word))
        (fun result => pure (booleanReply result)) : SailM Bool) := by
  apply congrArg (fun (tail : MemoryWriteWP.WriteResult → SailM Bool) =>
    (.impure (.writeMem 8 (conditionalRequest a word)) tail : SailM Bool))
  funext result
  cases result with
  | Ok payload => rfl
  | Err error => cases error; rfl

theorem wp_write_ram [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    image fixed whole gen era cpu a (reserved physical new : BitVec 64) floors sets
    (k : Bool → SailM Unit) post (ram : deviceAddress a = false)
    (members : ∀ j, j < 8 → nthByte new j ∈ sets j) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot a 8 reserved)) -∗
      pinWindow capacity era a physical (.own 1) floors sets -∗
      continuation capacity image fixed whole gen era cpu a new floors sets (k true) post -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (LeanPaperStock.Functions.write_ram .Write_RISCV_conditional
          (.Physaddr a) 8 new () >>= k)) post) := by
  have emit : (LeanPaperStock.Functions.write_ram .Write_RISCV_conditional
      (.Physaddr a) 8 new () >>= k) =
      (.impure (.writeMem 8 (conditionalRequest a new))
        (fun result => k (booleanReply result)) : SailM Unit) := by
    rw [write_ram_eq]
    apply congrArg (fun (tail : MemoryWriteWP.WriteResult → SailM Unit) =>
      (.impure (.writeMem 8 (conditionalRequest a new)) tail : SailM Unit))
    funext result
    cases result with
    | Ok payload => rfl
    | Err error => cases error; rfl
  rw [emit]
  simpa only [conditionalRequest, booleanReply, _root_.Sail.ArchSem.Effect.ret,
    _root_.Sail.ConcurrencyInterfaceV1.Free.instEffectEvent,
    _root_.Sail.ConcurrencyInterfaceV1.Free.Event.Result] using wp_write (hlc := hlc) capacity image fixed whole gen era cpu (conditionalRequest a new)
    reserved physical new floors sets
    (fun result => k (booleanReply result))
    post rfl ram rfl members

theorem actual [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : Spec capacity :=
  ⟨held_word_agreement capacity, wp_write capacity, wp_write_ram capacity⟩

end MachCSL.Logic.TsoPinnedWriteWP
