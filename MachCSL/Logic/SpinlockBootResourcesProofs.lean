import MachCSL.Logic.SpinlockBootResourcesDefs
import MachCSL.Logic.BootWindowProofs
import MachCSL.Machine.SpinlockImageProofs

namespace MachCSL.Logic.SpinlockBootResources
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine
open Iris.Std.PartialMap
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem codeWords_length : codeWords.length = 17 := by simp [codeWords]
theorem words_length : words.length = 19 := by simp [words, codeWords]

theorem mem_words (w : BootWindow.Word) : w ∈ words ↔
    (∃ i, codeWord i = w) ∨ w = lockWord ∨ w = counterWord := by
  simp only [words, codeWords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn]

theorem word_size (w : BootWindow.Word) (member : w ∈ words) : w.size = 4 := by
  obtain ⟨i, rfl⟩ | rfl | rfl := (mem_words w).mp member <;> rfl

theorem wordKeys_nodup : (BootWindow.wordKeys words).Nodup := by decide

theorem word_bounds (w : BootWindow.Word) (member : w ∈ words) : w.size ≤ 2 ^ 64 := by
  rw [word_size w member]
  decide

theorem word_ram (w : BootWindow.Word) (member : w ∈ words) (j : Nat) (bound : j < w.size) :
    Tso.AddrIsRAM (addressAdd w.address j) := by
  obtain ⟨i, rfl⟩ | rfl | rfl := (mem_words w).mp member
  · have ib := i.isLt
    change j < 4 at bound
    unfold Tso.AddrIsRAM
    simp only [codeWord, addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat, SpinlockImage.instruction_address]
    omega
  · change j < 4 at bound
    unfold Tso.AddrIsRAM
    simp only [lockWord, SpinlockImage.lockAddress, addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · change j < 4 at bound
    unfold Tso.AddrIsRAM
    simp only [counterWord, SpinlockImage.counterAddress, addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- All nineteen reads are the existing actual loaded-image certificates. -/
theorem word_read (w : BootWindow.Word) (member : w ∈ words) :
    readBytes (loadedRam SpinlockImage.image) w.address w.size = some w.value := by
  obtain ⟨i, rfl⟩ | rfl | rfl := (mem_words w).mp member
  · exact SpinlockImage.instruction_bytes i
  · exact SpinlockImage.lock_initial
  · exact SpinlockImage.counter_initial

theorem boot_lookup (g : State) (facts : BootFacts SpinlockImage.image g)
    (memory : Tso.AddressMap Byte) (decoded : Memory.FiniteMap.decode memory = g.memory)
    (w : BootWindow.Word) (member : w ∈ words) (j : Nat) (bound : j < w.size) :
    get? memory (addressAdd w.address j) = some (nthByte w.value j) := by
  have loaded : Memory.FiniteMap.decode memory = loadedRam SpinlockImage.image :=
    decoded.trans facts.2.1
  have atByte := congrFun loaded (addressAdd w.address j)
  change get? memory (addressAdd w.address j) = _ at atByte
  rw [atByte]
  exact readBytes_spec _ _ _ _ (word_read w member) j bound

theorem boot_time_lookup (g : State) (facts : BootFacts SpinlockImage.image g)
    (memory : Tso.AddressMap Byte) (decoded : Memory.FiniteMap.decode memory = g.memory)
    (w : BootWindow.Word) (member : w ∈ words) (j : Nat) (bound : j < w.size) :
    get? (Tso.Interp.bootTimestamps memory) (addressAdd w.address j) = some (0, Tso.payNone) := by
  have found := boot_lookup g facts memory decoded w member j bound
  change memory[addressAdd w.address j]? = _ at found
  change (Tso.Interp.bootTimestamps memory)[addressAdd w.address j]? = _
  simp only [Tso.Interp.bootTimestamps, _root_.Std.ExtTreeMap.getElem?_map, found, Option.map_some]

variable {GF : BundledGFunctors} (capacity : TsoStore.Capacity GF) (names : TsoStore.Names)

theorem windows_split :
    iprop(([∗list] w ∈ words, TsoStore.storedWindow capacity names w.address w.size w.value 0) ⊣⊢
      windows capacity names) := by
  unfold words windows codeWindows lockWindow counterWindow
  rw [BigSepL.bigSepL_append.to_eq, BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_nil.to_eq]
  simp only [lockWord, counterWord]
  constructor
  · iintro ⟨Hcode, Hlock, Hcounter, _⟩
    iframe
  · iintro ⟨Hcode, Hlock, Hcounter⟩
    iframe

/-- Extract from the actual initial two maps once, retaining their exact
remainders. No new name, fragment, timestamp or authority is allocated. -/
theorem extract_initial (g : State) (facts : BootFacts SpinlockImage.image g)
    (memory : Tso.AddressMap Byte) (decoded : Memory.FiniteMap.decode memory = g.memory) :
    iprop(BootWindow.mapBytes capacity.heap.ledger names.tso.ledger.bytes memory ∗
      BootWindow.mapTimes capacity.heap.ledger names.tso.ledger.timestamps (Tso.Interp.bootTimestamps memory) ⊢
      windows capacity names ∗ remainder capacity names memory) := by
  iintro H
  ihave ⟨Hwindows, Hrest⟩ := BootWindow.extract_words capacity names words 0
    wordKeys_nodup word_bounds word_ram memory (Tso.Interp.bootTimestamps memory)
    (boot_lookup g facts memory decoded) (boot_time_lookup g facts memory decoded) $$ H
  unfold remainder
  iframe Hrest
  iapply (windows_split capacity names).mp
  iexact Hwindows

end MachCSL.Logic.SpinlockBootResources
