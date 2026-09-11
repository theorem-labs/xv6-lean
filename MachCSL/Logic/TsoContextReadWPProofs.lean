import MachCSL.Logic.TsoContextReadWPSpec
import MachCSL.Logic.TsoContextWordProofs
import MachCSL.Logic.MemoryReadWPProofs

namespace MachCSL.Logic.TsoContextReadWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- Actual nonexclusive event inversion, including uniqueness of the returned
word and the exact chosen-view successor. -/
theorem step_inv [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (req : MemoryReadWP.ReadRequest 8) (k : MemoryReadWP.ReadResult 8 → SailM Unit)
    (word : BitVec 64) (ram : deviceAddress req.pa = false)
    (plain : accessExclusive req.access_kind = false) (live : ThreadLive g gen)
    (readable : ∀ view, g.views cpu ≤ view → view ≤ g.log.length →
      ReadsBytes g.image g.log (hartAgent cpu) view req.pa 8 word)
    (events : List Observation) (next : Expr) (after : State) (forks : List Expr)
    (step : Step image (.hart gen cpu (.impure (.readMem 8 req) k)) g events next after forks) :
    ∃ view, g.views cpu ≤ view ∧ view ≤ g.log.length ∧
      next = .hart gen cpu (k (.Ok (word, none))) ∧
      after = TsoRead.advanceView g cpu view ∧ forks = [] ∧ events = [] := by
  obtain ⟨view, actual, lower, upper, reads, nextEq, stateEq, forkEq, eventEq⟩ :=
    MemoryReadWP.plain_step_inv image g gen cpu 8 req k ram plain live events next after forks step
  have same : actual = word := MemoryReadWP.readsBytes_unique reads (readable view lower upper)
  subst actual
  exact ⟨view, lower, upper, nextEq, stateEq, forkEq, eventEq⟩

theorem advance_frame (g : State) (cpu : CPU) (view : Nat) :
    (TsoRead.advanceView g cpu view).memory = g.memory ∧
    (TsoRead.advanceView g cpu view).log = g.log ∧
    (TsoRead.advanceView g cpu view).registers = g.registers ∧
    (TsoRead.advanceView g cpu view).reservations = g.reservations :=
  ⟨rfl, rfl, rfl, rfl⟩

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

/-- Open the complete live era and return its restoration wand. The full
native heap (including metadata) and timestamp/log authority justify all views. -/
theorem power_word_read (fixed : MachineInterp.FixedNames) (g : State) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId) (live : ThreadLive g gen)
    (a : PhysicalAddress) (dq : DFrac) (word : BitVec 64) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ a dq word -∗
      MachineInterp.powerInterp capacity fixed g ∗ running capacity era cpu ξ ∗
      wordPointsto capacity era ξ a dq word ∗ ⌜TsoContextWord.Readback g cpu a word⌝) := by
  iintro Hp Hcert Hrun Hword
  ihave ⟨Hera, Hrestore⟩ := MachineInterp.live_era_access capacity fixed g gen era live $$ Hp Hcert
  iunfold Era.interp at Hera
  icases Hera with ⟨Hregs, Hheap, Hdevice, Hdisk, Htso, Hresv, %valid⟩
  have gate := TsoContextWord.load_fact (contextCapacity capacity) (contextNames era)
    cpu ξ era.imageBytes g a dq word
  rw [show TsoContext.heapAt (contextCapacity capacity) (contextNames era) g =
    Era.heapInterpAt capacity.era era g from rfl] at gate
  rw [show Tso.Interp.tsoInterpAt (contextCapacity capacity).tso (contextNames era).tso
    era.imageBytes g = Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g from rfl] at gate
  ihave %reads := gate $$ Hheap Htso Hrun Hword
  ihave Hp : MachineInterp.powerInterp capacity fixed g $$ [Hrestore Hregs Hheap Hdevice Hdisk Htso Hresv]
  · iapply Hrestore
    unfold Era.interp
    iframe Hregs Hheap Hdevice Hdisk Htso Hresv
    ipureintro
    exact valid
  iframe Hp Hrun Hword
  ipureintro
  exact reads

/-- Discharge the existing all-successor ordinary-read rule from actual
running-context ownership. No caller-supplied access or readability oracle. -/
theorem wp_read [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    image fixed whole gen era cpu ξ (req : MemoryReadWP.ReadRequest 8)
    (k : MemoryReadWP.ReadResult 8 → SailM Unit) dq (word : BitVec 64) post
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa dq word -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.readMem 8 req) k)) post) := by
  iintro #Hcert Hrun Hword Hcontinue
  iapply MemoryReadWP.wp_ram_read_plain_ex capacity image fixed whole gen era cpu 8 req k
    (fun value => value = word) post ram plain $$ Hcert
  unfold MemoryReadWP.plainPremise
  iintro %g %live Hp
  ihave ⟨Hp, Hrun, Hword, %reads⟩ := power_word_read capacity fixed g gen era cpu ξ live
    req.pa dq word $$ Hp Hcert Hrun Hword
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  isplit
  · ipureintro
    intro view lower _upper
    exact ⟨word, (reads view lower).1, rfl⟩
  · iintro !>
    imod Hback
    imodintro
    iframe Hp
    iintro %view %value %_lower %_upper %_read %same Hreceipt
    subst value
    iapply Hcontinue $$ Hrun Hword Hreceipt

theorem actual [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : Spec capacity := ⟨wp_read capacity⟩

end MachCSL.Logic.TsoContextReadWP
