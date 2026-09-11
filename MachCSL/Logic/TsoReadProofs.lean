import MachCSL.Logic.TsoReadSpec
import MachCSL.Logic.EraStateLink
import MachCSL.Logic.TsoInterpProofs
import MachCSL.Logic.HeapProofs

namespace MachCSL.Logic.TsoRead
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine

theorem writeBack_view (g : State) (cpu : CPU) (view : Nat) :
    writeBack g cpu { focus g cpu with view := view } = advanceView g cpu view := by
  have same {α : Type} (f : CPU → α) : updateHart f cpu (f cpu) = f := by
    funext other
    by_cases h : other = cpu <;> simp [updateHart, h]
  simp only [writeBack, focus, advanceView, same]

theorem advanceView_here (g : State) (cpu : CPU) (view : Nat) :
    (advanceView g cpu view).views cpu = view := by simp [advanceView, updateHart]

theorem advanceView_memoryOK (g : State) (cpu : CPU) (view : Nat)
    (ok : MemoryOK g) (bound : view ≤ g.log.length) : MemoryOK (advanceView g cpu view) := by
  refine ⟨ok.1, ?_, ok.2.2⟩
  intro other
  by_cases h : other = cpu
  · subst other; simpa [advanceView, updateHart] using bound
  · simpa [advanceView, updateHart, h] using ok.2.1 other

theorem avf_advance_mono (g : State) (cpu : CPU) (view : Nat) (lower : g.views cpu ≤ view) :
    ∀ h, Tso.Interp.avf g h ≤ Tso.Interp.avf (advanceView g cpu view) h := by
  intro h
  unfold Tso.Interp.avf
  split
  · rename_i bound
    by_cases same : (⟨h, bound⟩ : CPU) = cpu
    · simp [advanceView, updateHart, same, lower]
    · simp [advanceView, updateHart, same]
  · exact Nat.le_refl _

variable {GF : BundledGFunctors}

instance pristineByte_persistent (capacity : Tso.Capacity GF) γ a :
    Persistent (pristineByte capacity γ a) := by unfold pristineByte; infer_instance
instance pristineByte_timeless (capacity : Tso.Capacity GF) γ a :
    Timeless (pristineByte capacity γ a) := by unfold pristineByte; infer_instance
instance pristineWindow_persistent (capacity : Tso.Capacity GF) γ a n :
    Persistent (pristineWindow capacity γ a n) := by unfold pristineWindow; infer_instance

theorem pristineByte_mint (capacity : Tso.Capacity GF) γ a :
    iprop(Tso.timestampElem capacity γ (.own 1) a (0, Tso.payNone) ⊢ |==>
      pristineByte capacity γ a) := by
  letI := capacity.timestamps
  unfold pristineByte
  iintro H
  iapply ghost_map_elem_persist (GF := GF) (K := PhysicalAddress) (V := Tso.TimestampElem) (H := Tso.AddressMap) γ a (.own 1) (0, Tso.payNone) $$ H

theorem tso_receipt (capacity : Tso.Interp.Capacity GF) (names : Tso.Interp.EraNames)
    (eraImage : ByteMap 64) (g : State) (cpu : CPU) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names eraImage g -∗
      Tso.Interp.tsoInterpAt capacity names eraImage g ∗
      Tso.Views.viewLB capacity.views names.views names.logLength (hartAgent cpu) (g.views cpu)) := by
  unfold Tso.Interp.tsoInterpAt
  iintro ⟨%timestamps, %entries, Hts, %domain, %tie, Hlog, %rep, Hlen, Hv, %ok⟩
  ihave ⟨Hv, Hlen, Hreceipt⟩ := Tso.Views.viewLB_get capacity.views names.views names.logLength
    (Tso.Interp.avf g) (hartAgent cpu) g.log.length (Tso.Interp.avf_bound g ok.1 _) $$ Hv Hlen
  rw [Tso.Interp.avf_hart]
  iframe
  ipureintro
  exact ⟨domain, tie, rep, ok⟩

theorem tso_advance (capacity : Tso.Interp.Capacity GF) (names : Tso.Interp.EraNames)
    (eraImage : ByteMap 64) (g : State) (cpu : CPU) (view : Nat)
    (lower : g.views cpu ≤ view) (upper : view ≤ g.log.length) :
    iprop(Tso.Interp.tsoInterpAt capacity names eraImage g ⊢ |==>
      (Tso.Interp.tsoInterpAt capacity names eraImage (advanceView g cpu view) ∗
        Tso.Views.viewLB capacity.views names.views names.logLength (hartAgent cpu) view)) := by
  iintro Htso
  iunfold Tso.Interp.tsoInterpAt at Htso
  ihave ⟨%timestamps, %entries, Hts, %domain, %tie, Hlog, %rep, Hlen, Hv, %ok⟩ := Htso
  imod Tso.Views.viewAuth_update capacity.views names.views (Tso.Interp.avf g)
    (Tso.Interp.avf (advanceView g cpu view)) (avf_advance_mono g cpu view lower) $$ Hv with Hv
  imodintro
  have newok : MemoryOK (advanceView g cpu view) ∧ (advanceView g cpu view).image = eraImage :=
    ⟨advanceView_memoryOK g cpu view ok.1 upper, ok.2⟩
  have receipt := tso_receipt capacity names eraImage (advanceView g cpu view) cpu
  rw [advanceView_here] at receipt
  iapply receipt
  unfold Tso.Interp.tsoInterpAt
  dsimp only [advanceView]
  iframe
  ipureintro
  exact ⟨domain, tie, rep, newok⟩


theorem era_advance (capacity : Era.Capacity GF) (era : Era.Record) (g : State) (cpu : CPU) (view : Nat)
    (lower : g.views cpu ≤ view) (upper : view ≤ g.log.length) :
    iprop(Era.interp capacity era g ⊢ |==>
      (Era.interp capacity era (advanceView g cpu view) ∗
        Tso.Views.viewLB capacity.views era.views era.logLength (hartAgent cpu) view)) := by
  unfold Era.interp
  iintro ⟨Hregs, Hheap, Hdev, Hdisk, Htso, Hr, %ok⟩
  imod tso_advance capacity.tso era.tsoNames era.imageBytes g cpu view lower upper $$ Htso with ⟨Htso, Hreceipt⟩
  imodintro
  have heap : Era.heapInterpAt capacity era (advanceView g cpu view) = Era.heapInterpAt capacity era g := rfl
  rw [heap]
  dsimp only [advanceView, Era.Capacity.tso, Era.Record.tsoNames]
  iframe
  ipureintro
  exact ok

theorem power_advance (capacity : MachineInterp.Capacity GF) (fixed : MachineInterp.FixedNames)
    (g : State) (gen : Nat) (era : Era.Record) (cpu : CPU) (view : Nat)
    (live : ThreadLive g gen) (lower : g.views cpu ≤ view) (upper : view ≤ g.log.length) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era ==∗
      MachineInterp.powerInterp capacity fixed (advanceView g cpu view) ∗
      Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view) := by
  iintro Hp Hcert
  iapply MachineInterp.live_update capacity fixed g (advanceView g cpu view) gen era live rfl rfl rfl
    iprop(True) _ (by
      iintro Hera _
      iapply era_advance capacity.era era g cpu view lower upper $$ Hera) $$ Hp Hcert []
  itrivial

theorem pristine_byte_read (capacity : Era.Capacity GF) (era : Era.Record) (g : State)
    (a : PhysicalAddress) (dq : DFrac) (byte : Byte) :
    iprop(⊢ Era.interp capacity era g -∗
      Tso.physBytePointsto capacity.heap.ledger era.heap a dq byte -∗
      pristineByte capacity.heap.ledger era.timestamps a -∗
      ⌜∀ h view, read g.image g.log h view a = some byte⌝) := by
  unfold Era.interp Era.heapInterpAt
  iintro ⟨_, ⟨%memory, Hheap, %rep⟩, _, _, Htso, _, _⟩ ⟨Hb, _⟩ Hpristine
  have heapValid := Heap.valid capacity.heap ⟨era.heap, era.metadata⟩ memory a dq byte
  rw [Heap.pointsto_eq_byteElem] at heapValid
  ihave %lookup := heapValid $$ Hheap Hb
  iunfold pristineByte at Hpristine
  have timestampValid := Tso.Interp.tsoInterpAt_timestamp_valid capacity.tso era.tsoNames era.imageBytes g a
    .discard (0, Tso.payNone)
  dsimp only [Era.Capacity.tso, Era.Record.tsoNames] at timestampValid
  dsimp only [Era.Capacity.tso, Era.Record.tsoNames]
  ihave %valid := timestampValid $$ Htso Hpristine
  obtain ⟨actual, hm, latest⟩ := Tso.timestampOK_latest valid
  have equal : actual = byte := by
    have hb : g.memory a = some byte := by rw [← rep]; exact lookup
    exact Option.some.inj (hm.symm.trans hb)
  subst actual
  ipureintro
  intro h view
  exact read_of_latest g.image g.log h view a 0 byte latest (visible_zero _ _ _)


theorem pristine_window_read (capacity : Era.Capacity GF) (era : Era.Record) (g : State)
    (a : PhysicalAddress) (n : Nat) (dq : DFrac) (word : BitVec (8 * n)) :
    iprop(⊢ Era.interp capacity era g -∗
      byteWindow capacity.heap.ledger era.heap a n dq word -∗
      pristineWindow capacity.heap.ledger era.timestamps a n -∗
      ⌜∀ h view, ReadsBytes g.image g.log h view a n word⌝) := by
  unfold byteWindow pristineWindow
  iintro Hera Hbytes Hpristine
  iapply pure_forall.mpr
  iintro %h
  iapply pure_forall.mpr
  iintro %view
  unfold ReadsBytes
  iapply pure_forall.mpr
  iintro %j
  iapply pure_imp.mpr
  iintro %bound
  have present : (List.range n)[j]? = some j := by simp [bound]
  ihave Hb := BigSepL.bigSepL_lookup present $$ Hbytes
  ihave Hp := BigSepL.bigSepL_lookup present $$ Hpristine
  ihave %reads := pristine_byte_read capacity era g (addressAdd a j) dq (nthByte word j) $$ Hera Hb Hp
  ipureintro
  exact reads h view

theorem pristine_window_mint (capacity : Tso.Capacity GF) γ a n :
    iprop(initialTimestampWindow capacity γ a n ⊢ |==> pristineWindow capacity γ a n) := by
  unfold initialTimestampWindow pristineWindow
  iintro H
  iapply BigSepL.bigSepL_bupd
  iapply BigSepL.bigSepL_mono_of_forall $$ H
  intro _ j
  exact pristineByte_mint capacity γ (addressAdd a j)

theorem power_pristine_read (capacity : MachineInterp.Capacity GF) (fixed : MachineInterp.FixedNames)
    (g : State) (gen : Nat) (era : Era.Record) (live : ThreadLive g gen)
    (a : PhysicalAddress) (n : Nat) (dq : DFrac) (word : BitVec (8 * n)) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      byteWindow capacity.era.heap.ledger era.heap a n dq word -∗
      pristineWindow capacity.era.heap.ledger era.timestamps a n -∗
      ⌜∀ h view, ReadsBytes g.image g.log h view a n word⌝) := by
  iintro Hp Hcert Hb Hpristine
  ihave ⟨Hera, _⟩ := MachineInterp.live_era_access capacity fixed g gen era live $$ Hp Hcert
  iapply pristine_window_read capacity.era era g a n dq word $$ Hera Hb Hpristine

theorem power_memoryOK (capacity : MachineInterp.Capacity GF) (fixed : MachineInterp.FixedNames)
    (g : State) (gen : Nat) (era : Era.Record) (live : ThreadLive g gen) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗ ⌜MemoryOK g⌝) := by
  iintro Hp Hcert
  ihave ⟨Hera, _⟩ := MachineInterp.live_era_access capacity fixed g gen era live $$ Hp Hcert
  iunfold Era.interp at Hera
  ihave ⟨_, _, _, _, Htso, _, _⟩ := Hera
  iapply Tso.Interp.tsoInterpAt_memoryOK capacity.era.tso era.tsoNames era.imageBytes g $$ Htso

theorem tsoReadSpec (capacity : MachineInterp.Capacity GF) : TsoReadSpec capacity :=
  ⟨power_advance capacity, pristine_window_read capacity.era, pristine_window_mint capacity.era.heap.ledger⟩

end MachCSL.Logic.TsoRead
