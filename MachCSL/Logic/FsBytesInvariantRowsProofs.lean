import MachCSL.Logic.FsBytesInvariantProofs

namespace MachCSL.Logic.FsBytesInvariant
open Iris Iris.BI
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (names : Names)

instance atHome_persistent home : Persistent (atHome capacity names home) := by unfold atHome; infer_instance
instance row_persistent : Persistent (row capacity names) := by unfold row; infer_instance
instance any_persistent : Persistent (any capacity names) := by unfold any; infer_instance
instance anyAt_persistent home : Persistent (anyAt capacity names home) := by unfold anyAt; infer_instance

theorem any_row : iprop(any capacity names ⊢ row capacity names) := by
  unfold any
  iintro ⟨Hrow, _⟩
  iexact Hrow

theorem any_seal : iprop(any capacity names ⊢ FsBlockGhost.exc_sealed capacity.blocks names.exceptions) := by
  unfold any
  iintro ⟨_, Hseal⟩
  iexact Hseal

theorem any_of : iprop(⊢ row capacity names -∗ FsBlockGhost.exc_sealed capacity.blocks names.exceptions -∗ any capacity names) := by
  unfold any
  iintro Hr Hs
  iframe

theorem anyAt_any home : iprop(anyAt capacity names home ⊢ any capacity names) := by
  unfold anyAt any
  iintro ⟨Hat, Hseal⟩
  iframe Hseal
  unfold row
  iexists home
  iexact Hat

theorem agree_any_q (E : CoPset) dq block bytes machinery (mask : (↑logN : CoPset) ⊆ E) :
    iprop(⊢ any capacity names -∗ FsBlocks.blockQ capacity.bytes names.bytes dq block bytes -∗
      FsBlockGhost.chalf capacity.blocks names block machinery ={E}=∗
      ⌜machinery = bytes⌝ ∗ FsBlocks.blockQ capacity.bytes names.bytes dq block bytes ∗
      FsBlockGhost.chalf capacity.blocks names block machinery) := by
  unfold any row atHome
  iintro ⟨⟨%home, %values, #Hi⟩, #Hseal⟩ Hb Hm
  iapply agree_q capacity names E home values dq block bytes machinery mask $$ Hi Hseal Hb Hm

theorem agree_any (E : CoPset) block bytes machinery (mask : (↑logN : CoPset) ⊆ E) :
    iprop(⊢ any capacity names -∗ FsBlocks.block capacity.bytes names.bytes block bytes -∗
      FsBlockGhost.chalf capacity.blocks names block machinery ={E}=∗
      ⌜machinery = bytes⌝ ∗ FsBlocks.block capacity.bytes names.bytes block bytes ∗
      FsBlockGhost.chalf capacity.blocks names block machinery) :=
  agree_any_q capacity names E (.own 1) block bytes machinery mask

theorem actual : Spec capacity :=
  ⟨range_home capacity, block_home capacity, fun names => home_open capacity names,
    fun names => agree capacity names, fun names => agree_exc capacity names,
    fun names => agree_q capacity names, any_row capacity, any_seal capacity,
    any_of capacity, anyAt_any capacity, agree_any capacity, agree_any_q capacity⟩

end MachCSL.Logic.FsBytesInvariant
