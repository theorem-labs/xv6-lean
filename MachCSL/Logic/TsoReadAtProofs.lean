import MachCSL.Logic.TsoReadAtDefs
import MachCSL.Logic.TsoReadProofs

namespace MachCSL.Logic.TsoReadAt
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors}

theorem view_bound (capacity : Era.Capacity GF) (era : Era.Record) (g : State)
    (cpu : CPU) (time : Nat) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes g -∗
      Tso.Views.viewLB capacity.views era.views era.logLength (hartAgent cpu) time -∗
      ⌜time ≤ g.views cpu⌝) := by
  unfold Tso.Interp.tsoInterpAt
  iintro ⟨%_timestamps, %_entries, _, _, _, _, _, _, Hv, _⟩ Hview
  have valid := Tso.Views.viewAuth_valid capacity.views era.views era.logLength
    (Tso.Interp.avf g) (hartAgent cpu) time
  rw [Tso.Interp.avf_hart] at valid
  dsimp only [Era.Capacity.tso, Era.Record.tsoNames]
  iapply valid $$ Hv Hview

/-- A timestamp receipt supplies visibility of the owned latest byte at every
read view allowed after the current CPU view. No initial timestamp is assumed. -/
theorem byte_read (capacity : Era.Capacity GF) (era : Era.Record) (g : State)
    (cpu : CPU) (a : PhysicalAddress) (dq : DFrac) (byte : Byte) (time : Nat)
    (pay : Tso.Payload) :
    iprop(⊢ Era.interp capacity era g -∗
      Tso.physBytePointsto capacity.heap.ledger era.heap a dq byte -∗
      Tso.timestampElem capacity.heap.ledger era.timestamps dq a (time, pay) -∗
      Tso.Views.viewLB capacity.views era.views era.logLength (hartAgent cpu) time -∗
      ⌜∀ view, g.views cpu ≤ view → read g.image g.log (hartAgent cpu) view a = some byte⌝) := by
  unfold Era.interp Era.heapInterpAt
  iintro ⟨_, ⟨%memory, Hheap, %decoded⟩, _, _, Htso, _, _⟩ ⟨Hb, _⟩ Htime Hview
  have heapValid := Heap.valid capacity.heap ⟨era.heap, era.metadata⟩ memory a dq byte
  rw [Heap.pointsto_eq_byteElem] at heapValid
  ihave %lookup := heapValid $$ Hheap Hb
  have timestampValid := Tso.Interp.tsoInterpAt_timestamp_valid capacity.tso era.tsoNames era.imageBytes g a dq (time, pay)
  dsimp only [Era.Capacity.tso, Era.Record.tsoNames] at timestampValid
  dsimp only [Era.Capacity.tso, Era.Record.tsoNames]
  ihave %valid := timestampValid $$ Htso Htime
  have viewValid := view_bound capacity era g cpu time
  dsimp only [Era.Capacity.tso, Era.Record.tsoNames] at viewValid
  ihave %bound := viewValid $$ Htso Hview
  obtain ⟨actual, value, latest⟩ := Tso.timestampOK_latest valid
  have equal : actual = byte := by
    have stored : g.memory a = some byte := by rw [← decoded]; exact lookup
    exact Option.some.inj (value.symm.trans stored)
  subst actual
  ipureintro
  intro view above
  exact read_of_latest g.image g.log (hartAgent cpu) view a time byte latest
    (visible_below _ _ _ _ (Nat.le_trans bound above))

theorem window_read (capacity : Era.Capacity GF) (era : Era.Record) (g : State)
    (cpu : CPU) (a : PhysicalAddress) (n : Nat) (dq : DFrac)
    (word : BitVec (8 * n)) (time : Nat) :
    iprop(⊢ Era.interp capacity era g -∗
      TsoRead.byteWindow capacity.heap.ledger era.heap a n dq word -∗
      timestampWindow capacity.heap.ledger era.timestamps a n dq time -∗
      Tso.Views.viewLB capacity.views era.views era.logLength (hartAgent cpu) time -∗
      ⌜∀ view, g.views cpu ≤ view → ReadsBytes g.image g.log (hartAgent cpu) view a n word⌝) := by
  unfold TsoRead.byteWindow timestampWindow
  iintro Hera Hbytes Htime Hview
  iapply pure_forall.mpr
  iintro %view
  iapply pure_imp.mpr
  iintro %above
  unfold ReadsBytes
  iapply pure_forall.mpr
  iintro %j
  iapply pure_imp.mpr
  iintro %inside
  have present : (List.range n)[j]? = some j := by simp [inside]
  ihave Hb := BigSepL.bigSepL_lookup present $$ Hbytes
  ihave ⟨%pay, Ht⟩ := BigSepL.bigSepL_lookup present $$ Htime
  ihave %reads := byte_read capacity era g cpu (addressAdd a j) dq (nthByte word j) time pay $$ Hera Hb Ht Hview
  ipureintro
  exact reads view above

/-- The same read fact in the current power generation. -/
theorem power_read (capacity : MachineInterp.Capacity GF) (fixed : MachineInterp.FixedNames)
    (g : State) (gen : Nat) (era : Era.Record) (live : ThreadLive g gen)
    (cpu : CPU) (a : PhysicalAddress) (n : Nat) (dq : DFrac)
    (word : BitVec (8 * n)) (time : Nat) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap a n dq word -∗
      timestampWindow capacity.era.heap.ledger era.timestamps a n dq time -∗
      Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) time -∗
      ⌜∀ view, g.views cpu ≤ view → ReadsBytes g.image g.log (hartAgent cpu) view a n word⌝) := by
  iintro Hp Hcert Hb Htime Hview
  ihave ⟨Hera, _⟩ := MachineInterp.live_era_access capacity fixed g gen era live $$ Hp Hcert
  iapply window_read capacity.era era g cpu a n dq word time $$ Hera Hb Htime Hview

end MachCSL.Logic.TsoReadAt
