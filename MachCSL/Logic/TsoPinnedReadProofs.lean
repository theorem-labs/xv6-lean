import MachCSL.Logic.TsoPinnedReadSpec
import MachCSL.Logic.TsoPinnedReadPure
import MachCSL.Logic.TsoInterpProofs

namespace MachCSL.Logic.TsoPinnedRead
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance ownAnchor_persistent names h a position :
    Persistent (ownAnchor capacity names h a position) := by
  unfold ownAnchor
  infer_instance

instance bootCredential_persistent names cpu bound :
    Persistent (bootCredential capacity names cpu bound) := by
  unfold bootCredential
  infer_instance

instance slotAnchor_persistent names a floor :
    Persistent (slotAnchor capacity names a floor) := by
  unfold slotAnchor
  infer_instance

theorem ownAnchor_intro (names : Names) (h : Agent) (a : PhysicalAddress)
    (index : Nat) (msg : Message 64) (byte : Byte)
    (value : msgByte msg a = some byte) (author : msg.author = h) :
    iprop(⊢ Tso.History.logElem capacity.history names.logEntries index msg -∗
      ownAnchor capacity names h a (index + 1)) := by
  iintro Hmsg
  unfold ownAnchor
  iexists index, msg, byte
  iframe
  ipureintro
  exact ⟨rfl, value, author⟩

theorem bootCredential_view (names : Names) (cpu : CPU) (bound : Nat) :
    iprop(⊢ Tso.Views.viewLB capacity.views names.views names.logLength (hartAgent cpu) bound -∗
      bootCredential capacity names cpu bound) := by
  unfold bootCredential
  iintro Hview
  iapply Iris.BI.or_intro_l
  iexact Hview

theorem bootCredential_boot (names : Names) (cpu : CPU) (bound : Nat)
    (boot : hartAgent cpu = 0) :
    iprop(⊢ Tso.Views.llb capacity.views names.logLength bound -∗
      bootCredential capacity names cpu bound) := by
  unfold bootCredential
  iintro Hlog
  iapply Iris.BI.or_intro_r
  iframe
  ipureintro
  exact boot

/-- Projection of the actual timestamp authority and its complete semantic tie. -/
theorem pin_valid (names : Names) (image : ByteMap 64) (g : State)
    (a : PhysicalAddress) (dq : DFrac) (byte : Byte) (time bound : Nat) (allowed : Tso.ByteSet) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      Tso.physLedgerPin capacity.ledger names.ledger a dq byte time bound allowed -∗
      ⌜Tso.PinOK g.image g.log a bound allowed⌝) := by
  iintro Htso ⟨_, Htime⟩
  ihave %valid := Tso.Interp.tsoInterpAt_timestamp_valid capacity names image g a dq
    (time, Tso.payPin allowed bound) $$ Htso Htime
  ipureintro
  exact Tso.timestampOK_pin valid rfl

/-- The native history fragment is tied to the machine's exact log list. -/
theorem ownAnchor_valid (names : Names) (image : ByteMap 64) (g : State)
    (h : Agent) (a : PhysicalAddress) (position : Nat) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      ownAnchor capacity names h a position -∗
      ⌜∃ byte, logByte g.image g.log position a = some byte ∧
        ∀ view, visible h view g.log position = true⌝) := by
  unfold Tso.Interp.tsoInterpAt ownAnchor
  iintro ⟨%_timestamps, %entries, _, _, _, Hlog, %rep, _, _, _⟩
    ⟨%index, %msg, %byte, %positionEq, Hmsg, %value⟩
  ihave %lookup := Tso.History.log_lookup_list capacity.history names.logEntries (.own 1)
    entries g.log index msg rep $$ Hlog Hmsg
  ipureintro
  refine ⟨byte, ?_, ?_⟩
  · simp [positionEq, logByte, lookup, value.1]
  · intro view
    rw [positionEq]
    exact visible_own h view g.log index msg lookup value.2

theorem author_read (names : Names) (image : ByteMap 64) (g : State)
    (h : Agent) (a : PhysicalAddress) (dq : DFrac) (byte : Byte) (time bound : Nat)
    (allowed : Tso.ByteSet) (position : Nat) (above : bound ≤ position) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      Tso.physLedgerPin capacity.ledger names.ledger a dq byte time bound allowed -∗
      ownAnchor capacity names h a position -∗
      ⌜∀ view, ∃ v, read g.image g.log h view a = some v ∧ v ∈ allowed⌝) := by
  iintro Htso Hpin Hown
  ihave %pin := pin_valid capacity names image g a dq byte time bound allowed $$ Htso Hpin
  ihave %anchor := ownAnchor_valid capacity names image g h a position $$ Htso Hown
  obtain ⟨initial, value, visible⟩ := anchor
  ipureintro
  exact pinOK_author g.image g.log a bound position initial allowed h pin above visible value

theorem view_bound (names : Names) (image : ByteMap 64) (g : State) (cpu : CPU) (bound : Nat) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      Tso.Views.viewLB capacity.views names.views names.logLength (hartAgent cpu) bound -∗
      ⌜bound ≤ g.views cpu⌝) := by
  unfold Tso.Interp.tsoInterpAt
  iintro ⟨%_timestamps, %_entries, _, _, _, _, _, _, Hv, _⟩ Hview
  have valid := Tso.Views.viewAuth_valid capacity.views names.views names.logLength
    (Tso.Interp.avf g) (hartAgent cpu) bound
  rw [Tso.Interp.avf_hart] at valid
  iapply valid $$ Hv Hview

/-- The source receipt-based pin projection permits any agent at the read view. -/
theorem receipt_read (names : Names) (image : ByteMap 64) (g : State)
    (cpu : CPU) (a : PhysicalAddress) (dq : DFrac) (byte : Byte)
    (time bound : Nat) (allowed : Tso.ByteSet) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      Tso.Views.viewLB capacity.views names.views names.logLength (hartAgent cpu) bound -∗
      Tso.physLedgerPin capacity.ledger names.ledger a dq byte time bound allowed -∗
      ⌜∀ h view, g.views cpu ≤ view → ∃ v,
        read g.image g.log h view a = some v ∧ v ∈ allowed⌝) := by
  iintro Htso Hview Hpin
  ihave %pin := pin_valid capacity names image g a dq byte time bound allowed $$ Htso Hpin
  ihave %floor := view_bound capacity names image g cpu bound $$ Htso Hview
  ipureintro
  intro h view above
  exact pin h view (by omega)

theorem slot_read (names : Names) (image : ByteMap 64) (g : State) (cpu : CPU)
    (a : PhysicalAddress) (n : Nat) (dq : DFrac) (value : Nat → Byte)
    (bound : Nat) (sets : Nat → Tso.ByteSet) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      bootCredential capacity names cpu bound -∗
      slotBytes capacity names a n dq value bound sets -∗ ⌜SlotReads g cpu a n sets⌝) := by
  unfold slotBytes SlotReads bootCredential slotAnchor
  iintro Htso Hcred Hbytes
  iapply pure_forall.mpr
  iintro %view
  iapply pure_imp.mpr
  iintro %above
  iapply pure_forall.mpr
  iintro %j
  iapply pure_imp.mpr
  iintro %inside
  have present : (List.range n)[j]? = some j := by simp [inside]
  ihave ⟨%floor, %time, %below, Hpin, Hanchor⟩ := BigSepL.bigSepL_lookup present $$ Hbytes
  icases Hcred with (Hview | Hboot)
  · ihave %boundView := view_bound capacity names image g cpu bound $$ Htso Hview
    ihave %pin := pin_valid capacity names image g (addressAdd a j) dq (value j) time floor
      (sets j) $$ Htso Hpin
    ipureintro
    exact pin (hartAgent cpu) view (by omega)
  · icases Hboot with ⟨%boot, _⟩
    icases Hanchor with (%zero | Hanchor)
    · ihave %pin := pin_valid capacity names image g (addressAdd a j) dq (value j) time floor
        (sets j) $$ Htso Hpin
      ipureintro
      exact pin (hartAgent cpu) view (by omega)
    · icases Hanchor with (Hown | Hview)
      · ihave %reads := author_read capacity names image g 0 (addressAdd a j) dq (value j)
          time floor (sets j) floor (Nat.le_refl _) $$ Htso Hpin Hown
        ipureintro
        rw [boot]
        exact reads view
      · have valid := view_bound capacity names image g cpu floor
        rw [boot] at valid
        ihave %boundView := valid $$ Htso Hview
        ihave %pin := pin_valid capacity names image g (addressAdd a j) dq (value j) time floor
          (sets j) $$ Htso Hpin
        ipureintro
        exact pin (hartAgent cpu) view (by omega)

/-- Pure read justification leaves all linear authority and pinned cells intact. -/
theorem slot_read_preserve (names : Names) (image : ByteMap 64) (g : State) (cpu : CPU)
    (a : PhysicalAddress) (n : Nat) (dq : DFrac) (value : Nat → Byte)
    (bound : Nat) (sets : Nat → Tso.ByteSet) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      bootCredential capacity names cpu bound -∗
      slotBytes capacity names a n dq value bound sets -∗
      Tso.Interp.tsoInterpAt capacity names image g ∗
      bootCredential capacity names cpu bound ∗ slotBytes capacity names a n dq value bound sets ∗
      ⌜SlotReads g cpu a n sets⌝) := by
  iintro Htso Hcred Hbytes
  ihave %reads := slot_read capacity names image g cpu a n dq value bound sets $$ Htso Hcred Hbytes
  iframe
  ipureintro
  exact reads

theorem word_read (names : Names) (image : ByteMap 64) (g : State) (cpu : CPU)
    (a : PhysicalAddress) (dq : DFrac) (word : BitVec 64)
    (bound : Nat) (sets : Nat → Tso.ByteSet) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      bootCredential capacity names cpu bound -∗
      slotWord capacity names a dq word bound sets -∗ ⌜SlotReads g cpu a 8 sets⌝) :=
  slot_read capacity names image g cpu a 8 dq (nthByte word) bound sets

theorem actual : ReadSpec capacity :=
  ⟨pin_valid capacity, author_read capacity, slot_read capacity, slot_read_preserve capacity⟩

end MachCSL.Logic.TsoPinnedRead
