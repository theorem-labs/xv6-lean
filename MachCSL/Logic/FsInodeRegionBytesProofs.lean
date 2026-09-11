import MachCSL.Logic.FsInodeRegionBytesDefs
import MachCSL.Logic.FsInodeRegionBootProofs
import MachCSL.Logic.FsInodeRegionCodecProofs
import MachCSL.Logic.FsBytesGammaProofs

namespace MachCSL.Logic.FsInodeRegion
open Iris Iris.Std Iris.BI Xv6.Fs MachCSL.Memory
variable {GF : BundledGFunctors}

theorem encoded_records_row (view : FsView.View GF) b off records
    (wf : ∀ record ∈ records, record.WellFormed) :
    FsView.byteRange view b off (inodeBlockBytes records) ⊣⊢
      bigSepL (fun i record => FsView.byteRange view b (off + 64 * (i : Int)) (dinodeBytes record)) records := by
  induction records generalizing off with
  | nil => exact .rfl
  | cons record records ih =>
    rw [inodeBlockBytes, (FsView.byteRange_append view b off _ _).to_eq,
      dinodeBytes_length record (wf record (by simp))]
    rw [show ((64 : Nat) : Int) = 64 by decide]
    rw [(ih (off + 64) (fun dn member => wf dn (by simp [member]))).to_eq,
      BigSepL.bigSepL_cons.to_eq]
    have head : off + 64 * ((0 : Nat) : Int) = off := by omega
    rw [head]
    apply sep_congr_right
    apply BiEntails.of_eq
    apply BigSepL.bigSepL_eq_of_forall_eq
    intro k dn
    congr 1
    omega

theorem indexed_records_row (view : FsView.View GF) b off records :
    bigSepL (fun i record => FsView.byteRange view b (off + 64 * (i : Int)) (dinodeBytes record)) records ⊣⊢
    bigSepL (fun _ (i : Nat) => FsView.byteRange view b (off + 64 * (i : Int)) (dinodeBytes (records[i]?.getD default))) (List.range records.length) := by
  induction records generalizing off with
  | nil => exact .rfl
  | cons record records ih =>
    rw [List.length_cons, List.range_succ_eq_map, BigSepL.bigSepL_cons.to_eq,
      BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_map]
    simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ]
    have lhs : (fun (k : Nat) (dn : Dinode) => FsView.byteRange view b (off + 64 * ((k + 1 : Nat) : Int)) (dinodeBytes dn)) =
      (fun (k : Nat) dn => FsView.byteRange view b ((off + 64) + 64 * (k : Int)) (dinodeBytes dn)) := by
      funext k dn
      congr 1
      omega
    have rhs : (fun (_ : Nat) (k : Nat) => FsView.byteRange view b (off + 64 * ((k + 1 : Nat) : Int)) (dinodeBytes (records[k]?.getD default))) =
      (fun (_ : Nat) (k : Nat) => FsView.byteRange view b ((off + 64) + 64 * (k : Int)) (dinodeBytes (records[k]?.getD default))) := by
      funext j k
      congr 1
      omega
    rw [lhs, rhs]
    exact sep_congr_right (ih (off + 64))

theorem recs_block (view : FsView.View GF) start bi records (wf : InodeBlockWellFormed records) :
    recs view start bi records ⊣⊢ FsView.blockOwned view (start + (bi : Int)) (inodeBlockBytes records) := by
  have block : FsView.blockOwned view (start + (bi : Int)) (inodeBlockBytes records) ⊣⊢
      FsView.byteRange view (start + (bi : Int)) 0 (inodeBlockBytes records) := by
    unfold FsView.blockOwned
    constructor
    · iintro ⟨_, H⟩; iexact H
    · iintro H
      isplitr [H]
      · ipureintro; rw [inodeBlockBytes_length records wf.2, wf.1]
      · iexact H
  rw [block.to_eq]
  rw [(encoded_records_row view _ 0 records wf.2).to_eq,
    (indexed_records_row view _ 0 records).to_eq, wf.1]
  unfold recs
  apply BiEntails.of_eq
  apply BigSepL.bigSepL_eq
  intro k i found
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  have ibound : i < 16 := by simpa using (List.mem_range.mp (List.mem_of_getElem? found))
  have quotient : (16 * (bi : Int) + (i : Int)) / 16 = bi := by omega
  have remainder : (16 * (bi : Int) + (i : Int)) % 16 = i := by omega
  simp [FsState.recOwnedAt, FsState.recOwnedAtQ, FsView.byteRange, quotient, remainder]

theorem recs_logged_block (dc : Disk.Capacity GF) (names : FsBlocks.Names) start bi records
    (wf : InodeBlockWellFormed records) :
    recs (FsBytesGamma.logged dc names) start bi records ⊣⊢
      FsBlocks.block dc names.bytes (start + (bi : Int)) (inodeBlockBytes records) :=
  (recs_block _ start bi records wf).trans (FsBytesGamma.block dc names _ _)

/-- Reindexing preserves every list entry, including defaults only outside its
finite range (which this conjunction never visits). -/
theorem list_rows {A : Type} [Inhabited A] (f : Nat → A → IProp GF) (xs : List A) :
    bigSepL f xs = bigSepL (fun _ (i : Nat) => f i (xs[i]?.getD default)) (List.range xs.length) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons, List.range_succ_eq_map, BigSepL.bigSepL_cons.to_eq,
      BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_map]
    simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ]
    rw [ih (fun k x => f (k + 1) x)]

theorem region_bytes_recs (view : FsView.View GF) start blocks records (decoded : Decoded blocks records) :
    regionBytes view start blocks ⊣⊢ regionRecs view start records := by
  unfold regionBytes regionRecs
  rw [list_rows (fun bi bytes => FsView.blockOwned view (start + (bi : Int)) bytes) blocks,
    list_rows (fun bi ds => recs view start bi ds) records, decoded.1]
  apply BiEntails.of_eq
  apply BigSepL.bigSepL_eq
  intro k bi found
  have bound := List.mem_range.mp (List.mem_of_getElem? found)
  have wf : InodeBlockWellFormed (records[bi]?.getD []) := by
    apply decoded.2.1
    have hb : bi < records.length := by rw [decoded.1]; exact bound
    simpa only [List.getElem?_eq_getElem hb, Option.getD_some] using List.getElem_mem hb
  exact (congrArg (FsView.blockOwned view (start + (bi : Int))) (decoded.2.2 bi bound)).trans
    (recs_block view start bi _ wf).symm.to_eq

/-- Record-camera allocation plus exact byte factoring only. Complete inode
slots, escrow registry and region invariant are not among these conclusions. -/
theorem bootstrap_prelude (capacity : Capacity GF) (view : FsView.View GF) start blocks
    (full : ∀ block ∈ blocks, block.length = 1024)
    (bound : 16 * (blocks.length : Int) ≤ 2 ^ 32)
    (counts : Int → Nat) (imageRecords : Int → Dinode)
    (checks : ∀ records, Decoded blocks records → InodeRegionImage.Premises records blocks.length counts imageRecords)
    (frame : IProp GF) :
    iprop(regionBytes view start blocks ∗ frame ⊢ |==> ∃ g records,
      ⌜Decoded blocks records ∧ InodeRegionImage.Premises records blocks.length counts imageRecords⌝ ∗
      auth capacity g (initialMap records blocks.length) ∗ bootCells capacity g records blocks.length ∗
      regionRecs view start records ∗ frame) := by
  have decoded : Decoded blocks (decodeImage blocks) := image_decode blocks full
  iintro ⟨Hbytes, HR⟩
  ihave Hrecords := (region_bytes_recs view start blocks (decodeImage blocks) decoded).mp $$ Hbytes
  imod boot_allocate capacity (decodeImage blocks) blocks.length bound frame $$ HR with ⟨%g, Ha, Hcells, HR⟩
  imodintro
  iexists g, (decodeImage blocks)
  isplitr [Ha Hcells Hrecords HR]
  · ipureintro; exact ⟨decoded, checks _ decoded⟩
  · iframe Ha Hcells Hrecords HR

end MachCSL.Logic.FsInodeRegion
