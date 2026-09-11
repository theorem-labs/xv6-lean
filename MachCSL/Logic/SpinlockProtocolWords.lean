import MachCSL.Logic.SpinlockProtocolSpec
import MachCSL.Logic.TsoStoreProofs
import MachCSL.Logic.TsoReadAtProofs
import MachCSL.Logic.MemoryExclusiveWPProofs

namespace MachCSL.Logic.SpinlockProtocol
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

def stampsAt (era : Era.Record) (a : PhysicalAddress) (t : Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range 4,
    Tso.timestampElem capacity.machine.era.heap.ledger era.timestamps (.own 1)
      (addressAdd a j) (t, Tso.payNone))

/-- Exact, reversible separation: no full timestamp is made discarded. -/
theorem wordAt_split (era : Era.Record) (a : PhysicalAddress) (v : BitVec 32) (t : Nat) :
    wordAt capacity era a v t ⊣⊢
      TsoRead.byteWindow capacity.machine.era.heap.ledger era.heap a 4 (.own 1) v ∗
      stampsAt capacity era a t := by
  unfold wordAt TsoStore.storedWindow TsoStore.storedByte TsoRead.byteWindow stampsAt
  exact BigSepL.bigSepL_sep_eqv

theorem stamps_window (era : Era.Record) (a : PhysicalAddress) (t : Nat) :
    stampsAt capacity era a t ⊢
      TsoReadAt.timestampWindow capacity.machine.era.heap.ledger era.timestamps a 4 (.own 1) t := by
  unfold stampsAt TsoReadAt.timestampWindow
  apply BigSepL.bigSepL_mono_of_forall
  intro index j
  iintro H
  iexists Tso.payNone
  iexact H

theorem wordAt_ledger (era : Era.Record) (a : PhysicalAddress) (v : BitVec 32) (t : Nat) :
    wordAt capacity era a v t ⊢ TsoStore.ledgerWindow (storeCapacity capacity) (storeNames era) a 4 v :=
  TsoStore.storedWindow_ledger (storeCapacity capacity) (storeNames era) a 4 v t

theorem word_current (era : Era.Record) (g : State) (a : PhysicalAddress) (v : BitVec 32) (t : Nat) :
    iprop(⊢ Era.heapInterpAt capacity.machine.era era g -∗ wordAt capacity era a v t -∗
      ⌜readBytes g.memory a 4 = some v⌝) := by
  iintro Hheap Hword
  ihave ⟨Hbytes, Htime⟩ := (wordAt_split capacity era a v t).mp $$ Hword
  iapply MemoryExclusiveWP.heap_window_read capacity.machine era g a 4 (.own 1) v $$ Hheap Hbytes

/-- A real owned timestamp is bounded by the actual log, using one of the
four present bytes. It is not a protocol-side timestamp assumption. -/
theorem word_timestamp_bound (era : Era.Record) (g : State) (a : PhysicalAddress)
    (v : BitVec 32) (t : Nat) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes g -∗
      wordAt capacity era a v t -∗ ⌜t ≤ g.log.length⌝) := by
  iintro Htso Hword
  ihave ⟨Hbytes, Htime⟩ := (wordAt_split capacity era a v t).mp $$ Hword
  iunfold stampsAt at Htime
  ihave Hstamp := BigSepL.bigSepL_lookup (show (List.range 4)[0]? = some 0 by rfl) $$ Htime
  have valid := Tso.Interp.tsoInterpAt_timestamp_valid capacity.machine.era.tso era.tsoNames era.imageBytes
    g (addressAdd a 0) (.own 1) (t, Tso.payNone)
  dsimp only [Era.Capacity.tso, Era.Record.tsoNames] at valid
  dsimp only [Era.Capacity.tso, Era.Record.tsoNames]
  ihave %ok := valid $$ Htso Hstamp
  obtain ⟨byte, _, latest⟩ := Tso.timestampOK_latest ok
  ipureintro
  exact logByte_some_le g.image g.log t (addressAdd a 0) byte latest.1

theorem word_visible (fixed : MachineInterp.FixedNames) (g : State) (gen : Nat)
    (era : Era.Record) (live : ThreadLive g gen) (cpu : CPU) (a : PhysicalAddress)
    (v : BitVec 32) (t : Nat) :
    iprop(⊢ MachineInterp.powerInterp capacity.machine fixed g -∗
      MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      wordAt capacity era a v t -∗
      Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) t -∗
      ⌜∀ view, g.views cpu ≤ view → ReadsBytes g.image g.log (hartAgent cpu) view a 4 v⌝) := by
  iintro Hpower Hcert Hword Hview
  ihave ⟨Hbytes, Htime⟩ := (wordAt_split capacity era a v t).mp $$ Hword
  ihave Htime := stamps_window capacity era a t $$ Htime
  iapply TsoReadAt.power_read capacity.machine fixed g gen era live cpu a 4 (.own 1) v t $$
    Hpower Hcert Hbytes Htime Hview

end MachCSL.Logic.SpinlockProtocol
