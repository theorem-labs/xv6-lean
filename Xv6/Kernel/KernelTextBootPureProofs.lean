import Xv6.Kernel.KernelTextBootSpec
import Xv6.Kernel.KernelTextImagePureProofs
import Xv6.Kernel.Correspondence
import MachCSL.Logic.BootWindowProofs

namespace Xv6.Kernel.KernelTextBoot
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
open Iris.Std.PartialMap Xv6.Generated.KernelMaps
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 65536

theorem address_add (a : Int) (j : Nat) : addressAdd (address a) j = address (a + (j : Int)) := by
  simp [addressAdd, address, KernelTextImage.address, BitVec.ofInt_add]

theorem run_bounds (run : ByteRun) (member : run ∈ runs) :
    0x80000000 ≤ run.base ∧ run.base + run.length ≤ 0x80007000 := by
  change run ∈ [codeRun0, codeRun1, codeRun2, codeRun3, codeRun4, codeRun5, codeRun6] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem address_nat (a : Int) (low : 0 ≤ a) (high : a < 2^64) : ((address a).toNat : Int) = a := by
  simp only [address, KernelTextImage.address, BitVec.toNat_ofInt]
  change ((a % 18446744073709551616).toNat : Int) = a
  have high' : a < 18446744073709551616 := high
  rw [Int.emod_eq_of_lt low high', Int.toNat_of_nonneg low]

theorem payload_bound (run : ByteRun) (member : run ∈ runs) : run.payload < 2^(8*run.length) := by
  change run ∈ [codeRun0, codeRun1, codeRun2, codeRun3, codeRun4, codeRun5, codeRun6] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem bytes (run : ByteRun) (member : run ∈ runs) (j : Nat) (_bound : j < run.length) :
    nthByte (descriptor run).value j = value (run.byte j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [descriptor, nthByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (payload_bound run member),
    value, KernelTextImage.value, Xv6.Machine.byteOfUInt8, ByteRun.byte,
    Nat.shiftRight_eq_div_pow]
  simp

theorem lengths : descriptors.map BootWindow.Word.size = [4096,4096,4096,4096,4096,2976,292] := rfl

theorem count : keys.length = 23748 := by
  simp only [keys, BootWindow.wordKeys, List.length_flatMap, BootWindow.keys,
    List.length_map, List.length_range]
  change (descriptors.map BootWindow.Word.size).sum = _
  rw [lengths]
  rfl

theorem member_bounds (run : ByteRun) (member : run ∈ runs) (pa : PhysicalAddress)
    (inside : pa ∈ BootWindow.keys (address run.base) run.length) :
    run.base ≤ (pa.toNat : Int) ∧ (pa.toNat : Int) < run.base + run.length := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp inside
  have hj := List.mem_range.mp hj
  have bounds := run_bounds run member
  rw [address_add, address_nat _ (by omega) (by omega)]
  omega

theorem ordered : runs.Pairwise (fun a b => a.base + (a.length : Int) ≤ b.base) := by decide

theorem unique : keys.Nodup := by
  change (runs.flatMap (fun run => BootWindow.keys (address run.base) run.length)).Nodup
  apply List.pairwise_flatMap.mpr
  constructor
  · intro run member
    have bounds := run_bounds run member
    exact BootWindow.keys_nodup _ _ (by omega)
  · apply List.Pairwise.imp_of_mem _ ordered
    intro a b ha hb before x hx y hy same
    have bx := member_bounds a ha x hx
    have by' := member_bounds b hb y hy
    subst y
    omega

theorem domain (pa : PhysicalAddress) : pa ∈ keys ↔ ∃ a b, sourceMap a = some b ∧ address a = pa := by
  change pa ∈ runs.flatMap (fun run => BootWindow.keys (address run.base) run.length) ↔ _
  constructor
  · intro inside
    obtain ⟨run, member, inside⟩ := List.mem_flatMap.mp inside
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp inside
    have hj := List.mem_range.mp hj
    refine ⟨run.base + j, run.byte j, KernelTextImage.listed_lookup run member j hj, ?_⟩
    exact (address_add _ _).symm
  · rintro ⟨a, b, found, rfl⟩
    obtain ⟨run, member, j, hj, rfl, _⟩ := KernelTextImage.lookup_listed a b found
    apply List.mem_flatMap.mpr
    exact ⟨run, member, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, address_add _ _⟩⟩

theorem ram (w : BootWindow.Word) (member : w ∈ descriptors) (j : Nat) (inside : j < w.size) :
    Tso.AddrIsRAM (addressAdd w.address j) := by
  obtain ⟨run, runMember, rfl⟩ := List.mem_map.mp member
  have bound := run_bounds run runMember
  change Tso.AddrIsRAM (addressAdd (address run.base) j)
  rw [address_add]
  have nat := address_nat (run.base + j) (by change j < run.length at inside; omega)
    (by change j < run.length at inside; omega)
  unfold Tso.AddrIsRAM
  change j < run.length at inside
  omega

theorem source_loaded (a : Int) (b : UInt8) (found : sourceMap a = some b) :
    loadedRam Xv6.Machine.bootImage (address a) = some (value b) := by
  have facts := KernelTextImage.text_address a b found
  have byte := Xv6.Machine.bootByte_present a b (Kernel.code_loaded a b found)
  have ram := (loadedRam_shape Xv6.Machine.bootImage).2
  have low : (ramLow : Int) ≤ a := by
    obtain ⟨run, member, j, bound, rfl, _⟩ := KernelTextImage.lookup_listed a b found
    have := run_bounds run member
    unfold ramLow
    omega
  have high : a < (ramHigh : Int) := by
    obtain ⟨run, member, j, bound, rfl, _⟩ := KernelTextImage.lookup_listed a b found
    have := run_bounds run member
    unfold ramHigh
    omega
  have result := ram a low high
  change loadedRam Xv6.Machine.bootImage (address a) = some (Xv6.Machine.bootByte a) at result
  rw [byte] at result
  exact result

theorem boot_lookup (g : State) (memory : Tso.AddressMap Byte)
    (facts : BootFacts Xv6.Machine.bootImage g) (decoded : FiniteMap.decode memory = g.memory)
    (w : BootWindow.Word) (member : w ∈ descriptors) (j : Nat) (inside : j < w.size) :
    get? memory (addressAdd w.address j) = some (nthByte w.value j) := by
  obtain ⟨run, runMember, rfl⟩ := List.mem_map.mp member
  change j < run.length at inside
  have found := source_loaded _ _ (KernelTextImage.listed_lookup run runMember j inside)
  have loaded := congrFun (decoded.trans facts.2.1) (addressAdd (address run.base) j)
  change get? memory (addressAdd (address run.base) j) = _ at loaded
  change get? memory (addressAdd (address run.base) j) = _
  rw [loaded, address_add, found, bytes run runMember j inside]

theorem boot_times (g : State) (memory : Tso.AddressMap Byte)
    (facts : BootFacts Xv6.Machine.bootImage g) (decoded : FiniteMap.decode memory = g.memory)
    (w : BootWindow.Word) (member : w ∈ descriptors) (j : Nat) (inside : j < w.size) :
    get? (Tso.Interp.bootTimestamps memory) (addressAdd w.address j) = some (0, Tso.payNone) := by
  have found := boot_lookup g memory facts decoded w member j inside
  change memory[addressAdd w.address j]? = _ at found
  change (Tso.Interp.bootTimestamps memory)[addressAdd w.address j]? = _
  simp only [Tso.Interp.bootTimestamps, _root_.Std.ExtTreeMap.getElem?_map, found, Option.map_some]

theorem outside {V : Type} (m : Tso.AddressMap V) (pa : PhysicalAddress) (absent : pa ∉ keys) :
    get? (JalBootResources.deleteKeys m keys) pa = get? m pa :=
  BootWindow.lookup_deleteKeys m keys pa absent

theorem actualPure : PureSpec :=
  ⟨lengths, count, unique, domain, bytes, ram, source_loaded, boot_lookup, boot_times, outside⟩

end Xv6.Kernel.KernelTextBoot
