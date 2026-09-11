import MachCSL.Logic.FsBytesInvariantRangeProofs
import MachCSL.Logic.DiskProofs

namespace MachCSL.Logic.FsBytesInvariant
open Iris Iris.Std Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)

instance cacheHalves_timeless cache : Timeless (cacheHalves capacity names cache) := by
  unfold cacheHalves
  infer_instance
instance body_timeless home values : Timeless (body capacity names home values) := by
  unfold body
  infer_instance

theorem body_intro logged cache exceptions home values
    (domain : FiniteMap.dom_set (S := BlockSet) cache = home)
    (full : ∀ block bytes, get? cache block = some bytes → bytes.length = 1024)
    (tie : bytes_tie_exc logged cache exceptions) (byteDomain : bytes_dom logged home)
    (exceptionHome : exceptions ⊆ home) (exceptionValues : bytes_exc_val logged values exceptions) :
    iprop(Disk.mapAuth capacity.bytes names.bytes logged ∗ cacheHalves capacity names cache ∗
      FsBlockGhost.exc_auth capacity.blocks names.exceptions exceptions ⊢ body capacity names home values) := by
  iintro ⟨Ha, HC, HX⟩
  unfold body
  iexists logged, cache, exceptions
  iframe Ha HC HX
  isplit
  · ipureintro; exact domain
  · isplit
    · ipureintro; exact full
    · isplit
      · ipureintro; exact tie
      · isplit
        · ipureintro; exact byteDomain
        · isplit
          · ipureintro; exact exceptionHome
          · ipureintro; exact exceptionValues

theorem block_lookup (logged : ByteMap) dq block bytes :
    iprop(⊢ Disk.mapAuth capacity.bytes names.bytes logged -∗
      FsBlocks.blockQ capacity.bytes names.bytes dq block bytes -∗
      ⌜bytes.length = 1024 ∧ PartialMap.submap (FsDurBytes.byteRun (block * 1024) bytes) logged⌝) := by
  iintro Ha Hb
  iunfold FsBlocks.blockQ at Hb
  icases Hb with ⟨%length, Hr⟩
  ihave %included := range_lookup capacity names logged dq block 0 bytes $$ Ha Hr
  ipureintro
  exact ⟨length, by simpa only [Int.add_zero] using included⟩

theorem cache_lookup_agree (cache : CacheMap) block bytes machinery (found : get? cache block = some bytes) :
    iprop(⊢ cacheHalves capacity names cache -∗ FsBlockGhost.chalf capacity.blocks names block machinery -∗
      ⌜machinery = bytes⌝) := by
  letI := capacity.blocks.cache
  iintro HC Hm
  iunfold cacheHalves at HC
  ihave Hc := BigSepM.bigSepM_lookup found $$ HC
  iunfold FsBlockGhost.chalf at Hm Hc
  iunfold FsBlockGhost.cacheElem at Hm Hc
  iapply ghost_map_elem_agree names.cache block (.own (1 : Qp).half) (.own (1 : Qp).half) machinery bytes $$ [$Hm $Hc]

theorem read_agree (logged : ByteMap) (cache : CacheMap) exceptions home dq block bytes machinery
    (domain : FiniteMap.dom_set (S := BlockSet) cache = home)
    (full : ∀ block bytes, get? cache block = some bytes → bytes.length = 1024)
    (tie : bytes_tie_exc logged cache exceptions) (byteDomain : bytes_dom logged home)
    (outside : block ∉ exceptions) :
    iprop(⊢ Disk.mapAuth capacity.bytes names.bytes logged -∗ cacheHalves capacity names cache -∗
      FsBlocks.blockQ capacity.bytes names.bytes dq block bytes -∗
      FsBlockGhost.chalf capacity.blocks names block machinery -∗ ⌜machinery = bytes⌝) := by
  iintro Ha HC Hb Hm
  ihave %homeMember := block_home capacity names logged home dq block bytes byteDomain $$ Ha Hb
  obtain ⟨stored, found⟩ := cache_home_lookup cache home block domain homeMember
  ihave %same := cache_lookup_agree capacity names cache block stored machinery found $$ HC Hm
  ihave %owned := block_lookup capacity names logged dq block bytes $$ Ha Hb
  ipureintro
  exact same.trans (byte_runs_agree (block * 1024) bytes stored logged
    (owned.1.trans (full block stored found).symm) owned.2 (tie block stored found outside)).symm

variable {hlc : HasLC} [InvGS_gen hlc GF]

instance invariant_persistent home values : Persistent (invariant capacity names home values) := by
  unfold invariant
  infer_instance

theorem home_open (E : CoPset) home values dq block bytes (mask : (↑logN : CoPset) ⊆ E) :
    iprop(⊢ invariant capacity names home values -∗
      FsBlocks.blockQ capacity.bytes names.bytes dq block bytes ={E}=∗
      ⌜block ∈ home⌝ ∗ FsBlocks.blockQ capacity.bytes names.bytes dq block bytes) := by
  iintro #Hi Hb
  iunfold invariant at Hi
  imod inv_acc (fsbN_sub E mask) $$ Hi with ⟨Hbody, Hclose⟩
  imod Hbody
  iunfold body at Hbody
  icases Hbody with ⟨%logged, %cache, %exceptions, Ha, HC, HX, %domain, %full, %tie, %byteDomain, %exceptionHome, %exceptionValues⟩
  ihave %member := block_home capacity names logged home dq block bytes byteDomain $$ Ha Hb
  imod Hclose $$ [Ha HC HX] with _
  · iintro !>
    iapply body_intro capacity names logged cache exceptions home values domain full tie byteDomain exceptionHome exceptionValues
    iframe
  · imodintro
    iframe Hb
    ipureintro
    exact member

theorem agree_q (E : CoPset) home values dq block bytes machinery (mask : (↑logN : CoPset) ⊆ E) :
    iprop(⊢ invariant capacity names home values -∗ FsBlockGhost.exc_sealed capacity.blocks names.exceptions -∗
      FsBlocks.blockQ capacity.bytes names.bytes dq block bytes -∗ FsBlockGhost.chalf capacity.blocks names block machinery
      ={E}=∗ ⌜machinery = bytes⌝ ∗ FsBlocks.blockQ capacity.bytes names.bytes dq block bytes ∗
      FsBlockGhost.chalf capacity.blocks names block machinery) := by
  iintro #Hi #Hseal Hb Hm
  iunfold invariant at Hi
  imod inv_acc (fsbN_sub E mask) $$ Hi with ⟨Hbody, Hclose⟩
  imod Hbody
  iunfold body at Hbody
  icases Hbody with ⟨%logged, %cache, %exceptions, Ha, HC, HX, %domain, %full, %tie, %byteDomain, %exceptionHome, %exceptionValues⟩
  ihave %empty := FsBlockGhost.sealed_empty capacity.blocks names.exceptions exceptions $$ HX Hseal
  ihave %same := read_agree capacity names logged cache exceptions home dq block bytes machinery
    domain full tie byteDomain (by simp [empty]) $$ Ha HC Hb Hm
  imod Hclose $$ [Ha HC HX] with _
  · iintro !>
    iapply body_intro capacity names logged cache exceptions home values domain full tie byteDomain exceptionHome exceptionValues
    iframe
  · imodintro
    iframe Hb Hm
    ipureintro
    exact same

theorem agree (E : CoPset) home values block bytes machinery (mask : (↑logN : CoPset) ⊆ E) :
    iprop(⊢ invariant capacity names home values -∗ FsBlockGhost.exc_sealed capacity.blocks names.exceptions -∗
      FsBlocks.block capacity.bytes names.bytes block bytes -∗ FsBlockGhost.chalf capacity.blocks names block machinery
      ={E}=∗ ⌜machinery = bytes⌝ ∗ FsBlocks.block capacity.bytes names.bytes block bytes ∗
      FsBlockGhost.chalf capacity.blocks names block machinery) :=
  agree_q capacity names E home values (.own 1) block bytes machinery mask

theorem agree_exc (E : CoPset) home values (exceptions : BlockSet) block bytes machinery
    (mask : (↑logN : CoPset) ⊆ E) (outside : block ∉ exceptions) :
    iprop(⊢ invariant capacity names home values -∗ FsBlockGhost.exc_own capacity.blocks names.exceptions exceptions -∗
      FsBlocks.block capacity.bytes names.bytes block bytes -∗ FsBlockGhost.chalf capacity.blocks names block machinery
      ={E}=∗ ⌜machinery = bytes⌝ ∗ FsBlockGhost.exc_own capacity.blocks names.exceptions exceptions ∗
      FsBlocks.block capacity.bytes names.bytes block bytes ∗ FsBlockGhost.chalf capacity.blocks names block machinery) := by
  iintro #Hi Hhandle Hb Hm
  iunfold FsBlocks.block at Hb
  iunfold invariant at Hi
  imod inv_acc (fsbN_sub E mask) $$ Hi with ⟨Hbody, Hclose⟩
  imod Hbody
  iunfold body at Hbody
  icases Hbody with ⟨%logged, %cache, %actualExceptions, Ha, HC, HX, %domain, %full, %tie, %byteDomain, %exceptionHome, %exceptionValues⟩
  ihave %sameExceptions := FsBlockGhost.exception_agree capacity.blocks names.exceptions actualExceptions exceptions $$ HX Hhandle
  ihave %same := read_agree capacity names logged cache actualExceptions home (.own 1) block bytes machinery
    domain full tie byteDomain (by simpa only [sameExceptions] using outside) $$ Ha HC Hb Hm
  imod Hclose $$ [Ha HC HX] with _
  · iintro !>
    iapply body_intro capacity names logged cache actualExceptions home values domain full tie byteDomain exceptionHome exceptionValues
    iframe
  · imodintro
    unfold FsBlocks.block
    iframe Hhandle Hb Hm
    ipureintro
    exact same

end MachCSL.Logic.FsBytesInvariant
