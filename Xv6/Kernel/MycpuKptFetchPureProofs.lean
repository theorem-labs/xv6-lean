import Xv6.Kernel.MycpuKptFetchSpec
import Xv6.Kernel.MycpuRegimeShellPlan
import Xv6.Kernel.MycpuFetchBytesProofs
import Xv6.Kernel.MycpuDecodeProofs
import Xv6.Kernel.KptFetchPureProofs

namespace Xv6.Kernel.MycpuKptFetch
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem footprint_unique shares : RegisterFootprint.Unique (footprint shares) :=
  KptFetch.unique (fetchShares shares)

theorem footprint_counts (shares : Shares) :
    (footprint shares).length = 7 ∧ (remainderFootprint shares).length = 43 := ⟨rfl,rfl⟩

theorem footprint_members (shares : Shares) (cell : Register × DFrac)
    (member : cell ∈ footprint shares) : cell ∈ MycpuRegimeShell.footprint shares := by
  simp only [footprint,fetchShares,KptFetch.footprint,KptFetchHalf.footprint,
    KptAddress.auxiliaryFootprint,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl
  all_goals simp [MycpuRegimeShell.footprint,MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint]

theorem configuration control cpu values (config : Config control)
    (facts : SupervisorBits.MsFacts (control .mstatus)) : KptFetch.Config (entry control cpu values) :=
  ⟨⟨⟨config.privilege,facts.2.1,config.pma,config.htif⟩,config.adue⟩,config.compressed⟩

theorem source_config control (privilege : control .cur_privilege = .Supervisor)
    (pma : control .pma_regions = pmaBoot) (htif : control .htif_tohost_base = none)
    (misa : control .misa = 0x800000000014112d#64)
    (environment : control .menvcfg = 0xa000000000000000#64) : Config control := by
  refine ⟨privilege,pma,htif,?_,?_⟩
  · rw [misa]; rfl
  · rw [environment]; rfl

theorem image_words (i : Fin 14) : readBytes (loadedRam Xv6.Machine.bootImage)
    (MycpuDecode.address i) (MycpuFetchBytes.width i) = some (MycpuFetchBytes.word i) :=
  MycpuFetchBytes.fetched_bytes i

theorem coverage :
    ((List.ofFn (fun i : Fin 14 => (List.range (MycpuFetchBytes.width i)).map
      (MycpuDecode.offset i + ·))).flatten).eraseDups = List.range 34 := MycpuFetchBytes.footprint_complete

theorem one_chunk : ∀ i : Fin 14, KptFetch.chunks (MycpuDecode.address i) (result i) = [MycpuDecode.address i] := by
  decide

theorem decode_identity (i : Fin 14) : decodeFetch (result i) = MycpuDecode.decode i := by
  unfold result MycpuFetch.result MycpuDecode.decode
  split <;> rfl

theorem decoded (i : Fin 14) :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (MycpuDecode.snapshot i) 1000 (decodeFetch (result i)) =
      some (MycpuDecode.decoded i) := by
  rw [decode_identity]
  exact MycpuDecode.decode_certificate i

theorem aligned_two : ∀ i : Fin 14, is_aligned_vaddr (.Virtaddr (MycpuDecode.address i)) 2 = true := by decide

theorem aligned_four : ∀ i : Fin 14, is_aligned_vaddr (.Virtaddr (MycpuDecode.address i)) 4 =
    decide (i.val ∈ [1,3,5,7,8,9,11,13]) := by decide

theorem fetched_low : ∀ i : Fin 14,
    KernelTextDatum.lowHalf (BitVec.ofNat 32 (MycpuFetchBytes.encoding i)) =
      BitVec.ofNat 16 (MycpuDecode.encoding i) := by decide

theorem nativePureSpec : PureSpec :=
  ⟨footprint_unique,footprint_counts,footprint_members,configuration,source_config,
    image_words,coverage,one_chunk,decode_identity,decoded⟩

end Xv6.Kernel.MycpuKptFetch
