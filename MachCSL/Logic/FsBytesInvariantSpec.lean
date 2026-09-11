import MachCSL.Logic.FsBytesInvariantDefs

namespace MachCSL.Logic.FsBytesInvariant
open Iris Iris.Std Iris.BI

structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  range_home : ∀ (names : Names) logged home (dq : DFrac) (block : Int) (offset : Nat) bytes,
    bytes_dom logged home → offset < 1024 → 0 < bytes.length →
    iprop(⊢ Disk.mapAuth capacity.bytes names.bytes logged -∗
      FsBlocks.byteRangeQ capacity.bytes names.bytes dq block (offset : Int) bytes -∗ ⌜block ∈ home⌝)
  block_home : ∀ (names : Names) logged home dq block bytes,
    bytes_dom logged home →
    iprop(⊢ Disk.mapAuth capacity.bytes names.bytes logged -∗
      FsBlocks.blockQ capacity.bytes names.bytes dq block bytes -∗ ⌜block ∈ home⌝)
  home_open : ∀ (names : Names) (E : CoPset) home values dq block bytes, (↑logN : CoPset) ⊆ E →
    iprop(⊢ invariant capacity names home values -∗
      FsBlocks.blockQ capacity.bytes names.bytes dq block bytes ={E}=∗
      ⌜block ∈ home⌝ ∗ FsBlocks.blockQ capacity.bytes names.bytes dq block bytes)
  agree : ∀ (names : Names) (E : CoPset) home values block bytes machinery, (↑logN : CoPset) ⊆ E →
    iprop(⊢ invariant capacity names home values -∗ FsBlockGhost.exc_sealed capacity.blocks names.exceptions -∗
      FsBlocks.block capacity.bytes names.bytes block bytes -∗ FsBlockGhost.chalf capacity.blocks names block machinery
      ={E}=∗ ⌜machinery = bytes⌝ ∗ FsBlocks.block capacity.bytes names.bytes block bytes ∗
      FsBlockGhost.chalf capacity.blocks names block machinery)
  agree_exc : ∀ (names : Names) (E : CoPset) home values (exceptions : BlockSet) (block : Int) bytes machinery,
    (↑logN : CoPset) ⊆ E → block ∉ exceptions →
    iprop(⊢ invariant capacity names home values -∗ FsBlockGhost.exc_own capacity.blocks names.exceptions exceptions -∗
      FsBlocks.block capacity.bytes names.bytes block bytes -∗ FsBlockGhost.chalf capacity.blocks names block machinery
      ={E}=∗ ⌜machinery = bytes⌝ ∗ FsBlockGhost.exc_own capacity.blocks names.exceptions exceptions ∗
      FsBlocks.block capacity.bytes names.bytes block bytes ∗ FsBlockGhost.chalf capacity.blocks names block machinery)
  agree_q : ∀ (names : Names) (E : CoPset) home values dq block bytes machinery, (↑logN : CoPset) ⊆ E →
    iprop(⊢ invariant capacity names home values -∗ FsBlockGhost.exc_sealed capacity.blocks names.exceptions -∗
      FsBlocks.blockQ capacity.bytes names.bytes dq block bytes -∗ FsBlockGhost.chalf capacity.blocks names block machinery
      ={E}=∗ ⌜machinery = bytes⌝ ∗ FsBlocks.blockQ capacity.bytes names.bytes dq block bytes ∗
      FsBlockGhost.chalf capacity.blocks names block machinery)
  any_row : ∀ (names : Names), iprop(any capacity names ⊢ row capacity names)
  any_seal : ∀ (names : Names), iprop(any capacity names ⊢ FsBlockGhost.exc_sealed capacity.blocks names.exceptions)
  any_of : ∀ (names : Names), iprop(⊢ row capacity names -∗ FsBlockGhost.exc_sealed capacity.blocks names.exceptions -∗ any capacity names)
  anyAt_any : ∀ (names : Names) home, iprop(anyAt capacity names home ⊢ any capacity names)
  agree_any : ∀ (names : Names) (E : CoPset) block bytes machinery, (↑logN : CoPset) ⊆ E →
    iprop(⊢ any capacity names -∗ FsBlocks.block capacity.bytes names.bytes block bytes -∗
      FsBlockGhost.chalf capacity.blocks names block machinery ={E}=∗
      ⌜machinery = bytes⌝ ∗ FsBlocks.block capacity.bytes names.bytes block bytes ∗
      FsBlockGhost.chalf capacity.blocks names block machinery)
  agree_any_q : ∀ (names : Names) (E : CoPset) dq block bytes machinery, (↑logN : CoPset) ⊆ E →
    iprop(⊢ any capacity names -∗ FsBlocks.blockQ capacity.bytes names.bytes dq block bytes -∗
      FsBlockGhost.chalf capacity.blocks names block machinery ={E}=∗
      ⌜machinery = bytes⌝ ∗ FsBlocks.blockQ capacity.bytes names.bytes dq block bytes ∗
      FsBlockGhost.chalf capacity.blocks names block machinery)

end MachCSL.Logic.FsBytesInvariant
