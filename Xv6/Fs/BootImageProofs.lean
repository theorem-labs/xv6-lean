import Xv6.Fs.BootImageDefs
import Xv6.Fs.ValidityProofs

namespace Xv6.Fs

theorem covIn_zero (cov : BlockSet) (ndisk : Nat) (h : CovIn cov ndisk) :
    (0 : Int) ∉ cov := by
  intro hz
  have := (h 0 hz).1
  omega

theorem covIn_mono (left right : BlockSet) (ndisk : Nat)
    (subset : ∀ b, b ∈ left → b ∈ right) (h : CovIn right ndisk) :
    CovIn left ndisk := fun b hb => h b (subset b hb)

theorem covIn_disk_mono (cov : BlockSet) (small large : Nat)
    (bound : small ≤ large) (h : CovIn cov small) : CovIn cov large := by
  intro b hb
  have := h b hb
  constructor <;> omega

theorem blockCoverage_mem (count : Nat) (b : Int) :
    b ∈ blockCoverage count ↔ 1 ≤ b ∧ b < (count : Int) := by
  simp only [blockCoverage, Std.ExtTreeSet.mem_ofList, List.contains_iff_mem,
    List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    constructor <;> omega
  · intro hb
    refine ⟨(b - 1).toNat, ?_, ?_⟩ <;> omega

theorem blockCoverage_covIn (count : Nat) :
    CovIn (blockCoverage count) (1024 * count) := by
  intro b hb
  have := (blockCoverage_mem count b).mp hb
  constructor <;> omega

theorem bootImage_superblock (h : BootImageWF disk ndisk sb nib cov) : SuperblockOK sb :=
  (superblockValid_iff sb).mp ((fsimgValid_iff (blocks disk) sb).mp h.image).superblock

theorem bootImage_coverage_below (h : BootImageWF disk ndisk sb nib cov)
    (b : Int) (member : b ∈ cov) : 0 < b ∧ b < sb.size := by
  have := h.coverage b member
  have := h.diskBound
  constructor <;> omega

theorem bootImage_coverage_exact (h : BootImageWF disk ndisk sb nib cov) (b : Int) :
    b ∈ cov ↔ 1 ≤ b ∧ b < sb.size := by
  constructor
  · intro hb
    have := bootImage_coverage_below h b hb
    constructor <;> omega
  · intro hb
    by_cases below : b < dataStart sb
    · exact h.metadata b ⟨hb.1, below⟩
    · exact h.data b ⟨by omega, hb.2⟩

theorem bootImage_bitmap_bound (h : BootImageWF disk ndisk sb nib cov)
    (b : Int) (member : b ∈ cov) : 0 < b ∧ b < 8 * 1024 := by
  have := bootImage_coverage_below h b member
  have := (bootImage_superblock h).oneBitmap
  constructor <;> omega

theorem bootImage_region_end (h : BootImageWF disk ndisk sb nib cov) :
    sb.inodestart + (nib : Int) = sb.bmapstart := by
  rw [h.rounded, (bootImage_superblock h).bmapstart]

/-- Endpoints zero and one both name no positive block. -/
theorem blockCoverage_zero : blockCoverage 0 = blockCoverage 1 := by rfl

/-- The named record is exactly the source's right-associated conjunction. -/
theorem bootImageWF_iff (disk : Disk) (ndisk : Nat) (sb : Superblock)
    (nib : Nat) (cov : BlockSet) : BootImageWF disk ndisk sb nib cov ↔
    fsimgValid (blocks disk) sb = true ∧ regionValid (blocks disk) sb nib = true ∧
    sb.ninodes ≤ 16 * (nib : Int) ∧ 16 * (nib : Int) ≤ 2 ^ 32 ∧ 0 < nib ∧
    (nib : Int) = sb.ninodes / 16 + 1 ∧ CovIn cov ndisk ∧
    (∀ b : Int, 1 ≤ b ∧ b < dataStart sb → b ∈ cov) ∧
    (∀ b : Int, dataStart sb ≤ b ∧ b < sb.size → b ∈ cov) ∧
    parseSuperblock (blocks disk) = some sb ∧ 16 * (nib : Int) ≤ 2 ^ 16 ∧
    (ndisk : Int) ≤ 1024 * sb.size ∧ linksEqual (blocks disk) sb = true ∧
    regionBare (blocks disk) sb nib = true ∧ rootNoSelf (blocks disk) sb = true := by
  constructor
  · intro h
    exact ⟨h.image, h.region, h.advertised, h.wordBound, h.positive, h.rounded,
      h.coverage, h.metadata, h.data, h.parsed, h.ushortBound, h.diskBound,
      h.links, h.bare, h.rootSelf⟩
  · rintro ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o⟩
    exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o⟩

/-- One missing byte of a covered block violates the source mint bound. -/
theorem coverage_rejects_short_disk : ¬ CovIn (blockCoverage 2) 2047 := by
  intro h
  have := h 1 ((blockCoverage_mem 2 1).mpr (by decide))
  omega

/-- Covering block zero violates the source condition even on a large disk. -/
theorem coverage_rejects_zero (ndisk : Nat) : ¬ CovIn (Std.ExtTreeSet.ofList [(0 : Int)]) ndisk := by
  intro h
  apply covIn_zero _ _ h
  simp

end Xv6.Fs
