import MachCSL.Logic.FsStateInodeDefs
import MachCSL.Logic.FsViewProofs
import MachCSL.Logic.FsLinkProofs

namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Xv6.Fs FsView
variable {GF : BundledGFunctors} (view : View GF)

instance recOwnedQ_timeless [GTimeless view] dq sb i dn : Timeless (recOwnedQ view dq sb i dn) := by
  unfold recOwnedQ; infer_instance
instance recOwned_timeless [GTimeless view] sb i dn : Timeless (recOwned view sb i dn) := by
  unfold recOwned; infer_instance
instance recOwnedAtQ_timeless [GTimeless view] dq istart z dn : Timeless (recOwnedAtQ view dq istart z dn) := by
  unfold recOwnedAtQ; infer_instance
instance recOwnedAt_timeless [GTimeless view] istart z dn : Timeless (recOwnedAt view istart z dn) := by
  unfold recOwnedAt; infer_instance
instance indOwnedQ_timeless [GTimeless view] dq n : Timeless (indOwnedQ view dq n) := by
  unfold indOwnedQ; split <;> infer_instance
instance indOwned_timeless [GTimeless view] n : Timeless (indOwned view n) := by
  unfold indOwned; infer_instance
instance inodeDatQ_timeless [GTimeless view] dq n : Timeless (inodeDatQ view dq n) := by
  unfold inodeDatQ; infer_instance
instance inodeDat_timeless [GTimeless view] n : Timeless (inodeDat view n) := by
  unfold inodeDat; infer_instance
instance inodePhi_timeless [GTimeless view] sb i n : Timeless (inodePhi view sb i n) := by
  unfold inodePhi; infer_instance
instance inodePhiAt_timeless [GTimeless view] istart z n : Timeless (inodePhiAt view istart z n) := by
  unfold inodePhiAt; infer_instance

theorem recOwned_one sb i dn : recOwned view sb i dn = recOwnedQ view (.own 1) sb i dn := rfl
theorem recOwnedAt_one istart z dn : recOwnedAt view istart z dn = recOwnedAtQ view (.own 1) istart z dn := rfl
theorem indOwned_one n : indOwned view n = indOwnedQ view (.own 1) n := rfl
theorem inodeDat_one n : inodeDat view n = inodeDatQ view (.own 1) n := rfl
theorem gammaQ_recOwned dq sb i dn : recOwned (gammaQ view dq) sb i dn = recOwnedQ view dq sb i dn := rfl
theorem gammaQ_recOwnedAt dq istart z dn : recOwnedAt (gammaQ view dq) istart z dn = recOwnedAtQ view dq istart z dn := rfl
theorem gammaQ_indOwned dq n : indOwned (gammaQ view dq) n = indOwnedQ view dq n := rfl
theorem gammaQ_inodeDat dq n : inodeDat (gammaQ view dq) n = inodeDatQ view dq n := rfl

theorem recOwnedAtQ_sb dq sb i dn (bound : 0 ≤ i ∧ i < 2 ^ 32) :
    recOwnedAtQ view dq sb.inodestart i dn = recOwnedQ view dq sb i dn := by
  have cast : ((BitVec.ofInt 32 i).toNat : Int) = i := by
    rw [BitVec.toNat_ofInt]
    change ((i % (2 ^ 32 : Int)).toNat : Int) = i
    rw [Int.emod_eq_of_lt bound.1 bound.2, Int.toNat_of_nonneg bound.1]
  simp only [recOwnedAtQ, recOwnedQ, inodeBlock, inodeSlot,
    Int.cast_ofNat_Int, Int.natCast_emod, cast, Int.add_comm]

theorem recOwnedAt_sb sb i dn (bound : 0 ≤ i ∧ i < 2 ^ 32) :
    recOwnedAt view sb.inodestart i dn = recOwned view sb i dn := recOwnedAtQ_sb view _ _ _ _ bound

theorem inodePhiAt_sb sb i n (bound : 0 ≤ i ∧ i < 2 ^ 32) :
    inodePhiAt view sb.inodestart i n = inodePhi view sb i n := by
  unfold inodePhiAt inodePhi
  rw [recOwnedAt_sb view sb i n.record bound]

theorem recOwnedAtQ_split (fractional : PhiFrac view) q1 q2 istart z dn :
    recOwnedAtQ view (.own (q1 + q2)) istart z dn ⊣⊢
      recOwnedAtQ view (.own q1) istart z dn ∗ recOwnedAtQ view (.own q2) istart z dn :=
  byteRangeQ_split view fractional q1 q2 _ _ _

theorem indOwnedQ_split (fractional : PhiFrac view) q1 q2 n :
    indOwnedQ view (.own (q1 + q2)) n ⊣⊢ indOwnedQ view (.own q1) n ∗ indOwnedQ view (.own q2) n := by
  unfold indOwnedQ
  split
  · exact sep_emp.symm
  · exact blockOwnedQ_split view fractional q1 q2 _ _

theorem inodeDatQ_split (fractional : PhiFrac view) q1 q2 n :
    inodeDatQ view (.own (q1 + q2)) n ⊣⊢
      inodeDatQ view (.own q1) n ∗ inodeDatQ view (.own q2) n := by
  unfold inodeDatQ
  have splitBlocks : (fun k bs => blockOwnedQ view (.own (q1 + q2)) (n.address k) bs) =
      (fun k bs => iprop(blockOwnedQ view (.own q1) (n.address k) bs ∗
        blockOwnedQ view (.own q2) (n.address k) bs)) := by
    funext k bs
    exact (blockOwnedQ_split view fractional q1 q2 _ _).to_eq
  rw [splitBlocks, BigSepM.bigSepM_sep_eq, (indOwnedQ_split view fractional q1 q2 n).to_eq]
  constructor
  · iintro ⟨⟨H1, H2⟩, ⟨Hi1, Hi2⟩⟩
    isplitl [H1 Hi1]
    · iframe H1 Hi1
    · iframe H2 Hi2
  · iintro ⟨⟨H1, Hi1⟩, ⟨H2, Hi2⟩⟩
    iframe H1 H2 Hi1 Hi2

theorem inodeDatQ_block_acc dq n k bytes (found : n.blocks[k]? = some bytes) :
    inodeDatQ view dq n ⊢ blockOwnedQ view dq (n.address k) bytes ∗
      (blockOwnedQ view dq (n.address k) bytes -∗ inodeDatQ view dq n) := by
  unfold inodeDatQ
  iintro ⟨Hblocks, Hind⟩
  ihave ⟨Hblock, Hback⟩ := (BigSepM.bigSepM_lookup_acc (M := SlotMap) found).mp $$ Hblocks
  isplitl [Hblock]
  · iexact Hblock
  · iintro Hblock
    ihave Hblocks := Hback $$ Hblock
    iframe Hblocks Hind

variable (capacity : FsLink.Capacity GF)

instance entTokAt_timeless self orphan name target ty : Timeless (entTokAt view capacity self orphan name target ty) := by
  unfold entTokAt; split <;> infer_instance
instance entTok_timeless self parent orphan isDirectory name target : Timeless (entTok view capacity self parent orphan isDirectory name target) := by
  unfold entTok; split <;> infer_instance
instance entToks_timeless i n markers : Timeless (entToks view capacity i n markers) := by
  unfold entToks; infer_instance
instance entToksNodot_timeless i n markers : Timeless (entToksNodot view capacity i n markers) := by
  unfold entToksNodot; infer_instance
instance entToksX_timeless i n : Timeless (entToksX view capacity i n) := by
  unfold entToksX; infer_instance
instance inodeGhost_timeless i n : Timeless (inodeGhost view capacity i n) := by
  unfold inodeGhost; infer_instance
instance inodeOwned_timeless [GTimeless view] sb i n : Timeless (inodeOwned view capacity sb i n) := by
  unfold inodeOwned; infer_instance

theorem gammaQ_inodeGhost dq i n :
    inodeGhost (gammaQ view dq) capacity i n = inodeGhost view capacity i n := rfl

theorem inodeOwned_local sb i n : inodeOwned view capacity sb i n ⊢ ⌜DurableNode.Local i n⌝ := by
  unfold inodeOwned inodeGhost
  iintro ⟨_, ⟨%ty, _, _, _, Hlocal⟩⟩
  iexact Hlocal

theorem inodeOwned_split sb i n :
    inodeOwned view capacity sb i n ⊣⊢ inodePhi view sb i n ∗ inodeGhost view capacity i n := .rfl

end MachCSL.Logic.FsState
