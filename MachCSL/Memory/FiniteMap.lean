import MachCSL.Memory.Bytes
import Std.Data.ExtTreeMap.Lemmas

/-!
A checked representation bridge between the existing byte-map functions and
Lean's extensional finite tree maps. This does not change production state types
and does not import Rocq/stdpp `gmap` into Lean. A future cross-prover translation
must connect that source representation separately.

`encodeOn` is the executable interface when an explicit support list is known.
`encodeAll` proves that every function on `BitVec width` has a finite-map
representation: its enumeration has `2^width` entries. It is a logical witness,
not a practical encoder for 64-bit memory, and is never evaluated at that width.
-/
namespace MachCSL.Memory.FiniteMap

abbrev Tree (width : Nat) := Std.ExtTreeMap (Address width) Byte

/-- Observe a tree map through the existing partial-function interface. -/
def decode (tree : Tree width) : ByteMap width := fun address => tree[address]?

/-- Encode the present bytes at explicit keys; duplicate keys are harmless. -/
def encodeOn (keys : List (Address width)) (memory : ByteMap width) : Tree width :=
  match keys with
  | [] => ∅
  | key :: rest => match memory key with
    | none => encodeOn rest memory
    | some byte => (encodeOn rest memory).insert key byte

/-- The caller accounts for every present byte; no assumption about values at
listed keys is imposed. -/
def Covers (keys : List (Address width)) (memory : ByteMap width) : Prop :=
  ∀ address byte, memory address = some byte → address ∈ keys

/-- Exhaustive finite-domain witness. Do not execute at machine address width. -/
def addresses (width : Nat) : List (Address width) :=
  List.ofFn (fun index : Fin (2 ^ width) => BitVec.ofFin index)

def encodeAll (memory : ByteMap width) : Tree width := encodeOn (addresses width) memory

/-- Std's tree-map union is RIGHT biased. Reversing its operands implements
our source-compatible left-biased byte-map overlay. -/
def overlayTrees (new old : Tree width) : Tree width := old ∪ new

def eraseByte (memory : ByteMap width) (address : Address width) : ByteMap width :=
  fun other => if other = address then none else memory other

def writeOffsetsTree (tree : Tree width) (address : Address width) (value : BitVec bits)
    (offsets : List Nat) : Tree width :=
  offsets.foldr (fun offset rest => rest.insert (addressAdd address offset) (nthByte value offset)) tree

def writeBytesTree (tree : Tree width) (address : Address width) (n : Nat)
    (value : BitVec bits) : Tree width := writeOffsetsTree tree address value (List.range n)

@[simp] theorem decode_empty : decode (∅ : Tree width) = empty := by
  funext address
  simp [decode, empty]

theorem decode_insert (tree : Tree width) (address : Address width) (byte : Byte) :
    decode (tree.insert address byte) = insert (decode tree) address byte := by
  funext other
  simp only [decode, Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq]
  simp only [insert, overlay, singleton]
  by_cases h : address = other
  · subst other
    simp
  · simp [h, Ne.symm h, decode]

theorem decode_erase (tree : Tree width) (address : Address width) :
    decode (tree.erase address) = eraseByte (decode tree) address := by
  funext other
  simp only [decode, Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq, eraseByte]
  by_cases h : address = other
  · subst other
    simp
  · simp [h, Ne.symm h]

@[simp] theorem decode_overlay (new old : Tree width) :
    decode (overlayTrees new old) = overlay (decode new) (decode old) := by
  funext address
  exact Std.ExtTreeMap.getElem?_union

/-- Complete lookup characterization, including unlisted keys. -/
theorem lookup_encodeOn (keys : List (Address width)) (memory : ByteMap width)
    (address : Address width) :
    (encodeOn keys memory)[address]? = if address ∈ keys then memory address else none := by
  induction keys with
  | nil => simp [encodeOn]
  | cons key rest ih =>
    cases hm : memory key with
    | none =>
      simp only [encodeOn, hm, ih, List.mem_cons]
      by_cases h : address = key
      · subst address
        simp [hm]
      · simp [h]
    | some byte =>
      simp only [encodeOn, hm, Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq, ih,
        List.mem_cons]
      by_cases h : address = key
      · subst address
        simp [hm]
      · simp [h, Ne.symm h]

theorem decode_encodeOn (keys : List (Address width)) (memory : ByteMap width)
    (cover : Covers keys memory) : decode (encodeOn keys memory) = memory := by
  funext address
  simp only [decode, lookup_encodeOn]
  by_cases h : address ∈ keys
  · simp [h]
  · simp only [h, ↓reduceIte]
    cases hm : memory address with
    | none => rfl
    | some byte => exact False.elim (h (cover address byte hm))

@[simp] theorem mem_addresses (address : Address width) : address ∈ addresses width := by
  apply List.mem_ofFn.mpr
  exact ⟨address.toFin, BitVec.ofFin_toFin address⟩

/-- Every partial function on finite-width addresses is represented exactly. -/
@[simp] theorem decode_encodeAll (memory : ByteMap width) : decode (encodeAll memory) = memory :=
  decode_encodeOn _ _ (fun address _ _ => mem_addresses address)

/-- Lookup extensionality makes decoding injective, not merely a simulation. -/
theorem decode_injective : Function.Injective (@decode width) := by
  intro left right h
  apply Std.ExtTreeMap.ext_getElem?
  exact congrFun h

theorem encodeOn_decode (keys : List (Address width)) (tree : Tree width)
    (cover : Covers keys (decode tree)) : encodeOn keys (decode tree) = tree :=
  decode_injective (decode_encodeOn keys (decode tree) cover)

@[simp] theorem encodeAll_decode (tree : Tree width) : encodeAll (decode tree) = tree :=
  decode_injective (decode_encodeAll (decode tree))

/-- Existing tree keys give a practical support list without enumerating addresses. -/
def keys (tree : Tree width) : List (Address width) := tree.toList.map Prod.fst

theorem keys_cover (tree : Tree width) : Covers (keys tree) (decode tree) := by
  intro address byte h
  obtain ⟨other, he, hm⟩ :=
    Std.ExtTreeMap.getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList.mp h
  have heq : address = other := Std.compare_eq_iff_eq.mp he
  subst other
  exact List.mem_map.mpr ⟨(address, byte), hm, rfl⟩

theorem encodeOn_keys_decode (tree : Tree width) : encodeOn (keys tree) (decode tree) = tree :=
  encodeOn_decode _ _ (keys_cover tree)

/-- Source-style domain membership agrees with the concrete map's key membership. -/
theorem domain_decode (tree : Tree width) (address : Address width) :
    Domain (decode tree) address ↔ address ∈ tree := by
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?]
  simp only [Domain, decode]
  cases tree[address]? <;> simp

theorem decode_writeOffsets (tree : Tree width) (address : Address width)
    (value : BitVec bits) (offsets : List Nat) :
    decode (writeOffsetsTree tree address value offsets) =
      writeOffsets (decode tree) address value offsets := by
  induction offsets with
  | nil => rfl
  | cons offset rest ih =>
    change decode ((writeOffsetsTree tree address value rest).insert
      (addressAdd address offset) (nthByte value offset)) =
      insert (writeOffsets (decode tree) address value rest)
        (addressAdd address offset) (nthByte value offset)
    rw [decode_insert, ih]

/-- The right-fold store correspondence retains wraparound collision priority. -/
theorem decode_writeBytes (tree : Tree width) (address : Address width) (n : Nat)
    (value : BitVec bits) :
    decode (writeBytesTree tree address n value) = writeBytes (decode tree) address n value :=
  decode_writeOffsets tree address value (List.range n)

end MachCSL.Memory.FiniteMap
