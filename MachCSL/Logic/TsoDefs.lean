import MachCSL.Memory.Proofs
import Std.Data.ExtTreeSet

/-!
Payloads and pure interpretation from `TsoMemPa.v` at xv6iris arxiv-v1,
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. All four timestamp payload arms
are retained; byte sets are extensional finite tree sets. These are data and
pure semantic predicates, not replacements for Iris ownership.
-/
namespace MachCSL.Logic.Tso
open MachCSL.Memory

abbrev ByteSet := Std.ExtTreeSet Byte

structure Window where
  base : PhysicalAddress
  n : Nat
  j : Nat
  clear : Nat → Byte
  authorWord : Agent → Nat → Byte
  own : Agent → Option Nat
  lo : Nat

structure Release where
  base : PhysicalAddress
  n : Nat
  j : Nat
  author : Agent
  lo : Nat
  floor : Nat → Nat
  floorValue : Nat → Byte
  history : List (Nat × (Nat → Byte))

structure WordPin where
  base : PhysicalAddress
  n : Nat
  j : Nat
  lo : Nat
  members : (Nat → Byte) → Prop

structure Payload where
  pin : Option (ByteSet × Nat)
  win : Option Window
  rel : Option Release
  pinw : Option WordPin

def payNone : Payload := ⟨none, none, none, none⟩
def payPin (allowed : ByteSet) (bound : Nat) : Payload :=
  ⟨some (allowed, bound), none, none, none⟩
def payWin (window : Window) : Payload := ⟨none, some window, none, none⟩
def payRel (release : Release) : Payload := ⟨none, none, some release, none⟩
def payPinw (pin : WordPin) : Payload := ⟨none, none, none, some pin⟩
abbrev TimestampElem := Nat × Payload

/-- Source `pin_ok`: all agents' reads above the bound land in the allowed set. -/
def PinOK (image : ByteMap 64) (log : WriteLog 64) (a : PhysicalAddress)
    (bound : Nat) (allowed : ByteSet) : Prop :=
  ∀ h view, bound ≤ view → ∃ byte, read image log h view a = some byte ∧ byte ∈ allowed

def OwnLastFloor (log : WriteLog 64) (bound : Nat) (h : Agent)
    (a : PhysicalAddress) (t : Nat) : Prop :=
  ∀ i m, bound ≤ i + 1 → log[i]? = some m → m.author = h →
    (msgByte m a).isSome → i + 1 ≤ t

/-- Source `win_ok1`, including its floor and per-agent own-last obligations. -/
def WindowOK (image : ByteMap 64) (log : WriteLog 64) (a : PhysicalAddress)
    (w : Window) : Prop :=
  a = addressAdd w.base w.j ∧ w.j < w.n ∧
  (∀ i m, w.lo ≤ i + 1 → log[i]? = some m → (msgByte m a).isSome →
    (∀ k, k < w.n → msgByte m (addressAdd w.base k) = some (w.clear k)) ∨
    (∀ k, k < w.n → msgByte m (addressAdd w.base k) = some (w.authorWord m.author k))) ∧
  (∀ k, k < w.n → (image (addressAdd w.base k)).isSome) ∧
  w.lo ≤ log.length ∧
  (∀ k, k < w.n → logByte image log w.lo (addressAdd w.base k) = some (w.clear k)) ∧
  (∀ h t, w.own h = some t → w.lo ≤ t ∧ t ≤ log.length ∧
    (∀ view, w.lo ≤ view → visible h view log t = true) ∧
    logByte image log t a = some (w.clear w.j) ∧ OwnLastFloor log w.lo h a t)

/-- Source `rel_ok1`; history functions and strict-above-floor tests are retained. -/
def ReleaseOK (image : ByteMap 64) (log : WriteLog 64) (a : PhysicalAddress)
    (r : Release) : Prop :=
  a = addressAdd r.base r.j ∧ r.j < r.n ∧ r.lo ≤ log.length ∧
  (∀ i m, r.lo < i + 1 → log[i]? = some m → (msgByte m a).isSome →
    ∃ f, (i + 1, f) ∈ r.history) ∧
  (∀ q f, (q, f) ∈ r.history → r.lo < q ∧
    ∃ i m, q = i + 1 ∧ log[i]? = some m ∧ m.author = r.author ∧
      ∀ k, k < r.n → msgByte m (addressAdd r.base k) = some (f k)) ∧
  (∀ k, k < r.n → (image (addressAdd r.base k)).isSome) ∧
  (∀ k, k < r.n → r.floor k ≤ r.lo ∧
    logByte image log (r.floor k) (addressAdd r.base k) = some (r.floorValue k) ∧
    ∀ t, r.floor k < t → t ≤ r.lo → logByte image log t (addressAdd r.base k) = none)

/-- Source `pinw_ok1`: the whole word belongs to a predicate, not a product of byte sets. -/
def WordPinOK (image : ByteMap 64) (log : WriteLog 64) (a : PhysicalAddress)
    (w : WordPin) : Prop :=
  a = addressAdd w.base w.j ∧ w.j < w.n ∧ 0 < w.n ∧
  (∀ i m, w.lo ≤ i + 1 → log[i]? = some m → (msgByte m a).isSome →
    ∃ f, w.members f ∧ ∀ k, k < w.n → msgByte m (addressAdd w.base k) = some (f k)) ∧
  w.lo ≤ log.length ∧
  (∃ f, w.members f ∧ ∀ k, k < w.n → logByte image log w.lo (addressAdd w.base k) = some (f k))

/-- Source `ts_ok`, with every payload implication preserved. -/
def TimestampOK (image memory : ByteMap 64) (log : WriteLog 64)
    (a : PhysicalAddress) (e : TimestampElem) : Prop :=
  (∃ byte, memory a = some byte ∧ Latest image log a e.1 byte) ∧
  (∀ allowed bound, e.2.pin = some (allowed, bound) → PinOK image log a bound allowed) ∧
  (∀ w, e.2.win = some w → WindowOK image log a w) ∧
  (∀ r, e.2.rel = some r → ReleaseOK image log a r) ∧
  (∀ w, e.2.pinw = some w → WordPinOK image log a w)

/-- Source `RiscvPtsto.addr_is_ram`, independent of any arbitrary RAM predicate. -/
def AddrIsRAM (a : PhysicalAddress) : Prop := 0x80000000 ≤ a.toNat ∧ a.toNat < 0x88000000

theorem pinOK_mint (latest : Latest image log a t byte) (ht : t ≤ bound)
    (member : byte ∈ allowed) : PinOK image log a bound allowed := by
  intro h view hv
  exact ⟨byte, read_of_latest image log h view a t byte latest
    (visible_below h view log t (Nat.le_trans ht hv)), member⟩

/-- Source `read_down_app_frame`: old log positions are unaffected by append. -/
theorem readDown_append_frame (image : ByteMap 64) (log : WriteLog 64)
    (m : Message 64) (h view : Nat) (a : PhysicalAddress) (t : Nat)
    (within : t ≤ log.length) :
    readDown image (log ++ [m]) h view a t = readDown image log h view a t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have vis : visible h view (log ++ [m]) (t + 1) = visible h view log (t + 1) := by
      simp only [visible, List.getElem?_append_left (by omega : t < log.length)]
    simp only [readDown, vis, logByte_append_below image log m (t + 1) a within]
    split
    · rfl
    · exact ih (by omega)

theorem pinOK_append (pin : PinOK image log a bound allowed)
    (entry : msgByte m a = none ∨ ∃ byte, msgByte m a = some byte ∧ byte ∈ allowed) :
    PinOK image (log ++ [m]) a bound allowed := by
  intro h view above
  change ∃ byte, readDown image (log ++ [m]) h view a (log ++ [m]).length = some byte ∧
    byte ∈ allowed
  simp only [List.length_append, List.length_singleton, readDown, logByte_top]
  cases hv : visible h view (log ++ [m]) (log.length + 1) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte,
      readDown_append_frame image log m h view a log.length (by omega)]
    exact pin h view above
  | true =>
    simp only [↓reduceIte]
    rcases entry with absent | ⟨byte, lookup, member⟩
    · simp only [absent, readDown_append_frame image log m h view a log.length (by omega)]
      exact pin h view above
    · exact ⟨byte, by simp [lookup], member⟩

theorem pinOK_append_frame (pin : PinOK image log a bound allowed) (absent : msgByte m a = none) :
    PinOK image (log ++ [m]) a bound allowed := pinOK_append pin (Or.inl absent)

theorem pinOK_mono (pin : PinOK image log a bound allowed) (higher : bound ≤ bound') :
    PinOK image log a bound' allowed := fun h view above => pin h view (Nat.le_trans higher above)

theorem timestampOK_latest (h : TimestampOK image memory log a e) :
    ∃ byte, memory a = some byte ∧ Latest image log a e.1 byte := h.1

theorem timestampOK_pin (h : TimestampOK image memory log a e)
    (pin : e.2.pin = some (allowed, bound)) : PinOK image log a bound allowed := h.2.1 _ _ pin

theorem timestampOK_win (h : TimestampOK image memory log a e)
    (win : e.2.win = some w) : WindowOK image log a w := h.2.2.1 _ win

theorem timestampOK_rel (h : TimestampOK image memory log a e)
    (rel : e.2.rel = some r) : ReleaseOK image log a r := h.2.2.2.1 _ rel

theorem timestampOK_pinw (h : TimestampOK image memory log a e)
    (pinw : e.2.pinw = some w) : WordPinOK image log a w := h.2.2.2.2 _ pinw

theorem timestampOK_unpinned (lookup : memory a = some byte)
    (latest : Latest image log a t byte) : TimestampOK image memory log a (t, payNone) := by
  exact ⟨⟨byte, lookup, latest⟩, by simp [payNone], by simp [payNone],
    by simp [payNone], by simp [payNone]⟩
end MachCSL.Logic.Tso
