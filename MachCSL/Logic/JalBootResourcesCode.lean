import MachCSL.Logic.JalBootResourcesMap
import MachCSL.Logic.TsoReadProofs

namespace MachCSL.Logic.JalBootResources
open Iris Iris.Std Iris.BI MachCSL.Machine MachCSL.Memory
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap

def codeKeys : List PhysicalAddress := [0x80000000, 0x80000001, 0x80000002, 0x80000003]
def codeValue (a : PhysicalAddress) : Byte := if a = jalImage.vector then 0x6f else 0

theorem codeKeys_nodup : codeKeys.Nodup := by decide
theorem codeKeys_range : codeKeys = (List.range 4).map (addressAdd jalImage.vector) := by decide

theorem codeValue_nth (j : Nat) (bound : j < 4) :
    codeValue (addressAdd jalImage.vector j) = nthByte 0x6f#32 j := by
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> decide

theorem codeKeys_ram (a : PhysicalAddress) (member : a ∈ codeKeys) : Tso.AddrIsRAM a := by
  simp only [codeKeys, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> unfold Tso.AddrIsRAM <;> decide

variable {GF : BundledGFunctors} (capacity : Tso.Capacity GF)

/-- The exact remaining full byte cells after removing the four instruction bytes. -/
def byteRemainder (γ : GName) (m : Tso.AddressMap Byte) : IProp GF :=
  iprop([∗map] a ↦ value ∈ deleteKeys m codeKeys, Tso.byteElem capacity γ (.own 1) a value)

def timestampRemainder (γ : GName) (m : Tso.AddressMap Byte) : IProp GF :=
  iprop([∗map] a ↦ value ∈ deleteKeys (Tso.Interp.bootTimestamps m) codeKeys,
    Tso.timestampElem capacity γ (.own 1) a value)

theorem extract_code_bytes (γ : GName) (m : Tso.AddressMap Byte)
    (lookup : ∀ a, a ∈ codeKeys → get? m a = some (codeValue a)) :
    iprop(⊢ ([∗map] a ↦ value ∈ m, Tso.byteElem capacity γ (.own 1) a value) -∗
      TsoRead.byteWindow capacity γ jalImage.vector 4 (.own 1) 0x6f#32 ∗ byteRemainder capacity γ m) := by
  iintro H
  ihave ⟨Hcode, Hrest⟩ := extract_keys
    (fun a value => Tso.byteElem capacity γ (.own 1) a value) codeKeys codeKeys_nodup codeValue m lookup $$ H
  unfold byteRemainder
  iframe Hrest
  unfold TsoRead.byteWindow
  isimp only [codeKeys_range] at Hcode
  isimp only [BigSepL.bigSepL_map] at Hcode
  iapply BigSepL.bigSepL_mono $$ Hcode
  intro j a present
  have bound : a < 4 := List.mem_range.mp (List.mem_of_getElem? present)
  have ram := codeKeys_ram (addressAdd jalImage.vector a) (by rw [codeKeys_range]; exact List.mem_map.mpr ⟨a, List.mem_range.mpr bound, rfl⟩)
  iintro H
  unfold Tso.physBytePointsto
  isimp only [codeValue_nth a bound] at H
  iframe H
  ipureintro; exact ram

theorem extract_code_timestamps (γ : GName) (m : Tso.AddressMap Byte)
    (lookup : ∀ a, a ∈ codeKeys → get? m a = some (codeValue a)) :
    iprop(⊢ ([∗map] a ↦ value ∈ Tso.Interp.bootTimestamps m,
        Tso.timestampElem capacity γ (.own 1) a value) -∗
      TsoRead.initialTimestampWindow capacity γ jalImage.vector 4 ∗ timestampRemainder capacity γ m) := by
  have found : ∀ a, a ∈ codeKeys → get? (Tso.Interp.bootTimestamps m) a = some (0, Tso.payNone) := by
    intro a member
    have eq := lookup a member
    change m[a]? = some (codeValue a) at eq
    change (Tso.Interp.bootTimestamps m)[a]? = _
    simp only [Tso.Interp.bootTimestamps, _root_.Std.ExtTreeMap.getElem?_map, eq, Option.map_some]
  iintro H
  ihave ⟨Hcode, Hrest⟩ := extract_keys
    (fun a value => Tso.timestampElem capacity γ (.own 1) a value)
    codeKeys codeKeys_nodup (fun _ => (0, Tso.payNone)) (Tso.Interp.bootTimestamps m) found $$ H
  unfold timestampRemainder
  iframe Hrest
  unfold TsoRead.initialTimestampWindow
  isimp only [codeKeys_range] at Hcode
  isimp only [BigSepL.bigSepL_map] at Hcode
  iexact Hcode

/-- All timestamp cells outside the instruction remain at full ownership. -/
theorem mint_code_timestamps (γ : GName) (m : Tso.AddressMap Byte)
    (lookup : ∀ a, a ∈ codeKeys → get? m a = some (codeValue a)) :
    iprop(⊢ ([∗map] a ↦ value ∈ Tso.Interp.bootTimestamps m,
        Tso.timestampElem capacity γ (.own 1) a value) ==∗
      TsoRead.pristineWindow capacity γ jalImage.vector 4 ∗ timestampRemainder capacity γ m) := by
  iintro H
  ihave ⟨Hcode, Hrest⟩ := extract_code_timestamps capacity γ m lookup $$ H
  imod TsoRead.pristine_window_mint capacity γ jalImage.vector 4 $$ Hcode with Hcode
  imodintro
  iframe

end MachCSL.Logic.JalBootResources
