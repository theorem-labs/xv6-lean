import Xv6.Kernel.MycpuBootResourcesSpec
import Xv6.Kernel.MycpuFetchBytesProofs
import MachCSL.Logic.BootWindowProofs

namespace Xv6.Kernel.MycpuBootResources
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine MachCSL.Logic
open Iris.Std.PartialMap
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1024

theorem span_bytes : ∀ j : Fin 34, nthByte spanWord j.val =
    Xv6.Machine.byteOfUInt8 (MycpuFetchBytes.bytes[j.val]'(by
      rw [MycpuFetchBytes.bytes_length]; exact j.isLt)) := by decide

theorem address_add (j : Nat) :
    addressAdd address j = BitVec.ofInt 64 (MycpuDecode.base + (j : Int)) := by
  simp [addressAdd, address, BitVec.ofInt_add]

theorem span_ram (j : Nat) (bound : j < 34) : Tso.AddrIsRAM (addressAdd address j) := by
  unfold Tso.AddrIsRAM
  change 0x80000000 ≤ (addressAdd (0x800018ba#64) j).toNat ∧
    (addressAdd (0x800018ba#64) j).toNat < 0x88000000
  simp only [addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem span_read : readBytes (loadedRam Xv6.Machine.bootImage) address 34 = some spanWord := by
  apply readBytes_of_bytes
  intro j bound
  rw [address_add, MycpuFetchBytes.ram_byte j bound, span_bytes ⟨j, bound⟩]

theorem keys_nodup : keys.Nodup := BootWindow.keys_nodup address 34 (by decide)

theorem fetch_address (i : Fin 14) :
    addressAdd address (MycpuDecode.offset i) = MycpuDecode.address i := by
  rw [address_add]
  rfl

theorem fetch_bytes (i : Fin 14) (j : Nat) (bound : j < MycpuFetchBytes.width i) :
    nthByte spanWord (MycpuDecode.offset i + j) = nthByte (MycpuFetchBytes.word i) j := by
  have inside : MycpuDecode.offset i + j < 34 := by have := MycpuFetchBytes.span_bound i; omega
  rw [span_bytes ⟨_, inside⟩, MycpuFetchBytes.word_bytes i ⟨j, bound⟩]

theorem boot_lookup (g : State) (facts : BootFacts Xv6.Machine.bootImage g)
    (memory : Tso.AddressMap Byte) (decoded : FiniteMap.decode memory = g.memory)
    (j : Nat) (bound : j < 34) :
    get? memory (addressAdd address j) = some (nthByte spanWord j) := by
  have loaded : FiniteMap.decode memory = loadedRam Xv6.Machine.bootImage := decoded.trans facts.2.1
  have atByte := congrFun loaded (addressAdd address j)
  change get? memory (addressAdd address j) = _ at atByte
  rw [atByte]
  exact readBytes_spec _ _ _ _ span_read j bound

theorem boot_time_lookup (g : State) (facts : BootFacts Xv6.Machine.bootImage g)
    (memory : Tso.AddressMap Byte) (decoded : FiniteMap.decode memory = g.memory)
    (j : Nat) (bound : j < 34) :
    get? (Tso.Interp.bootTimestamps memory) (addressAdd address j) = some (0, Tso.payNone) := by
  have found := boot_lookup g facts memory decoded j bound
  change memory[addressAdd address j]? = _ at found
  change (Tso.Interp.bootTimestamps memory)[addressAdd address j]? = _
  simp only [Tso.Interp.bootTimestamps, _root_.Std.ExtTreeMap.getElem?_map, found, Option.map_some]

variable {GF : BundledGFunctors} (capacity : TsoStore.Capacity GF) (names : TsoStore.Names)

theorem extract_initial (g : State) (facts : BootFacts Xv6.Machine.bootImage g)
    (memory : Tso.AddressMap Byte) (decoded : FiniteMap.decode memory = g.memory) :
    iprop(BootWindow.mapBytes capacity.heap.ledger names.tso.ledger.bytes memory ∗
      BootWindow.mapTimes capacity.heap.ledger names.tso.ledger.timestamps (Tso.Interp.bootTimestamps memory) ⊢
      rawSpan capacity names ∗ remainder capacity names memory) :=
  BootWindow.extract_stored capacity names memory (Tso.Interp.bootTimestamps memory) descriptor 0
    (by decide) span_ram (boot_lookup g facts memory decoded) (boot_time_lookup g facts memory decoded)

theorem remainder_byte_lookup (memory : Tso.AddressMap Byte) (a : PhysicalAddress) (outside : a ∉ keys) :
    get? (JalBootResources.deleteKeys memory keys) a = get? memory a :=
  BootWindow.lookup_deleteKeys memory keys a outside

theorem remainder_time_lookup (memory : Tso.AddressMap Byte) (a : PhysicalAddress) (outside : a ∉ keys) :
    get? (JalBootResources.deleteKeys (Tso.Interp.bootTimestamps memory) keys) a =
      get? (Tso.Interp.bootTimestamps memory) a :=
  BootWindow.lookup_deleteKeys _ keys a outside

end Xv6.Kernel.MycpuBootResources
