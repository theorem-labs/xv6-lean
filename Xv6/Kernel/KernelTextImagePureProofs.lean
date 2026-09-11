import Xv6.Kernel.KernelTextImageSpec
import Xv6.Kernel.Proofs
import Xv6.Kernel.MycpuFetchBytesProofs
import Xv6.Kernel.KernelMapStaticPureProofs

namespace Xv6.Kernel.KernelTextImage
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
open Xv6.Generated.KernelMaps
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem source (a : Int) : sourceMap a = listMap ((codeRuns.map ByteRun.entries).flatten) a :=
  runMap_eq_listMap codeRuns a

theorem listed_lookup (run : ByteRun) (member : run ∈ codeRuns) (j : Nat) (bound : j < run.length) :
    sourceMap (run.base + (j : Int)) = some (run.byte j) := by
  simp only [codeRuns, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [codeRun0, codeRun1, codeRun2, codeRun3, codeRun4, codeRun5, codeRun6] at bound ⊢
    simp only [sourceMap, codeRuns, runMap, List.foldr_cons, List.foldr_nil, Elf.union,
      ByteRun.lookup, codeRun0, codeRun1, codeRun2, codeRun3, codeRun4, codeRun5, codeRun6]
    try simp only [Int.add_sub_cancel, Int.toNat_natCast]
    split <;> try omega
    all_goals simp_all only [Option.orElse_some, Option.orElse_none]
    all_goals repeat' (split <;> try omega)
    all_goals simp_all
    all_goals congr 1 <;> omega

theorem lookup_listed (a : Int) (b : UInt8) (found : sourceMap a = some b) :
    ∃ run ∈ codeRuns, ∃ j, j < run.length ∧ a = run.base + (j : Int) ∧ b = run.byte j := by
  obtain ⟨run, member, found⟩ := runMap_some_exists codeRuns a b found
  obtain ⟨low, high, val⟩ := (run.lookup_some_iff a b).mp found
  refine ⟨run, member, (a - run.base).toNat, ?_, ?_, val.symm⟩ <;> omega

theorem text_address (a : Int) (b : UInt8) (found : sourceMap a = some b) :
    KernelDatum.Positive (address a) ∧ KernelTextDatum.AddrIsText (address a) := by
  obtain ⟨run, member, j, bound, rfl, _⟩ := lookup_listed a b found
  have bounds : 0x80000000 ≤ run.base ∧ run.base + run.length ≤ 0x80007000 := by
    simp only [codeRuns, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have low : 0 ≤ run.base + (j : Int) := by omega
  have high : run.base + (j : Int) < 2^64 := by omega
  have nat : (address (run.base + (j : Int))).toNat = (run.base + (j : Int)).toNat := by
    simp only [address, BitVec.toNat_ofInt]
    omega
  simp only [KernelDatum.Positive, KernelTextDatum.AddrIsText, KernelTextDatum.textEnd, nat]
  omega

theorem byte_count : (codeRuns.map ByteRun.length).sum = 23748 := by decide

theorem mycpu_bytes : ∀ i : Fin 14, ∀ j : Fin (MycpuFetchBytes.width i),
    ∃ b, sourceMap (MycpuDecode.base + ((MycpuDecode.offset i + j.val : Nat) : Int)) = some b ∧
      value b = nthByte (MycpuFetchBytes.word i) j.val := by
  decide

theorem actualPure : PureSpec := ⟨source, listed_lookup, lookup_listed, text_address, byte_count, mycpu_bytes⟩

end Xv6.Kernel.KernelTextImage
