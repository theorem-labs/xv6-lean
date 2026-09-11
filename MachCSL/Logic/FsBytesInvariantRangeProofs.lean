import MachCSL.Logic.FsBytesInvariantPureProofs
import MachCSL.Logic.FsBlockGhostProofs
import MachCSL.Logic.FsDurBytesLedgerProofs

namespace MachCSL.Logic.FsBytesInvariant
open Iris Iris.Std Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)

theorem range_map dq block offset bytes :
    FsBlocks.byteRangeQ capacity.bytes names.bytes dq block offset bytes ⊣⊢
      bigSepM (M := Disk.ImageMap) (fun address value => FsBlocks.byteElem capacity.bytes names.bytes dq address value)
        (FsDurBytes.byteRun (block * 1024 + offset) bytes) := by
  exact (BigSepM.bigSepM_map_seqZ (M' := Disk.ImageMap)
    (Φ := fun address value => FsBlocks.byteElem capacity.bytes names.bytes dq address value)
    (start := block * 1024 + offset) (l := bytes)).symm

theorem range_lookup (logged : ByteMap) dq block offset bytes :
    iprop(⊢ Disk.mapAuth capacity.bytes names.bytes logged -∗
      FsBlocks.byteRangeQ capacity.bytes names.bytes dq block offset bytes -∗
      ⌜PartialMap.submap (FsDurBytes.byteRun (block * 1024 + offset) bytes) logged⌝) := by
  letI := capacity.bytes.image
  iintro Ha Hr
  ihave Hr := (range_map capacity names dq block offset bytes).mp $$ Hr
  iunfold Disk.mapAuth at Ha
  unfold FsBlocks.byteElem
  iapply ghost_map_lookup_big (GF := GF) (H := Disk.ImageMap) (dq' := dq)
    (FsDurBytes.byteRun (block * 1024 + offset) bytes) $$ Ha Hr

theorem range_home (logged : ByteMap) (home : BlockSet) dq (block : Int) (offset : Nat) (bytes : List Byte)
    (domain : bytes_dom logged home) (off : offset < 1024) (nonempty : 0 < bytes.length) :
    iprop(⊢ Disk.mapAuth capacity.bytes names.bytes logged -∗
      FsBlocks.byteRangeQ capacity.bytes names.bytes dq block (offset : Int) bytes -∗ ⌜block ∈ home⌝) := by
  iintro Ha Hr
  ihave %included := range_lookup capacity names logged dq block (offset : Int) bytes $$ Ha Hr
  ipureintro
  exact range_home_pure logged home block offset bytes domain off nonempty included

theorem block_home (logged : ByteMap) (home : BlockSet) dq (block : Int) (bytes : List Byte)
    (domain : bytes_dom logged home) :
    iprop(⊢ Disk.mapAuth capacity.bytes names.bytes logged -∗
      FsBlocks.blockQ capacity.bytes names.bytes dq block bytes -∗ ⌜block ∈ home⌝) := by
  iintro Ha Hb
  iunfold FsBlocks.blockQ at Hb
  icases Hb with ⟨%length, Hr⟩
  iapply range_home capacity names logged home dq block 0 bytes domain (by decide) (by omega) $$ Ha Hr

end MachCSL.Logic.FsBytesInvariant
