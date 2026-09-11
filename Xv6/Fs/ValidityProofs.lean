import Xv6.Fs.ValiditySpec
import Xv6.Fs.BitmapProofs
import Xv6.Fs.LinksProofs

namespace Xv6.Fs

theorem fsimgValid_iff image sb : fsimgValid image sb = true ↔ FsimgChecks image sb := by
  simp only [fsimgValid, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨a,b⟩,c⟩,d⟩,e⟩,f⟩,g⟩,h⟩
    exact ⟨a,b,c,d,e,f,g,h⟩
  · rintro ⟨a,b,c,d,e,f,g,h⟩
    exact ⟨⟨⟨⟨⟨⟨⟨a,b⟩,c⟩,d⟩,e⟩,f⟩,g⟩,h⟩

theorem fsimgValid_superblock image sb (valid : fsimgValid image sb = true) : SuperblockOK sb :=
  (superblockValid_iff sb).mp ((fsimgValid_iff image sb).mp valid).superblock

theorem fsimgValid_log image sb (valid : fsimgValid image sb = true) :
    MachCSL.Memory.assembleBytes ((image sb.logstart).take 4) = 0 :=
  (logClean_iff image sb).mp ((fsimgValid_iff image sb).mp valid).log

theorem fsimgValid_inode image sb i (valid : fsimgValid image sb = true)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (live : (dinode image sb i).typeZ ≠ 0) :
    InodeOK image sb (dinode image sb i) :=
  inodesValid_spec image sb i ((fsimgValid_iff image sb).mp valid).inodes bound live

theorem fsimgValid_used image sb (valid : fsimgValid image sb = true) :
    ∃ used, usedSet image sb = some used ∧ (usedBlocks image sb).Nodup ∧
      bitmapValid image sb used = true := by
  have h := ((fsimgValid_iff image sb).mp valid).blocks
  unfold blocksBitmapValid at h
  cases eq : usedSet image sb with
  | none => simp only [eq, Bool.false_eq_true] at h
  | some used => exact ⟨used, rfl, usedSet_nodup image sb used eq, by simpa only [eq] using h⟩

theorem fsimgValid_dir image sb i (valid : fsimgValid image sb = true)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (directory : (dinode image sb i).typeZ = 1) :
    DirectoryOK image sb i (dinode image sb i) :=
  dirsValid_spec image sb ((fsimgValid_iff image sb).mp valid).directories i bound directory

theorem fsimgValid_root image sb (valid : fsimgValid image sb = true) : rootValid image sb = true :=
  ((fsimgValid_iff image sb).mp valid).root

theorem fsimgValid_dots image sb i (valid : fsimgValid image sb = true)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (directory : (dinode image sb i).typeZ = 1) :
    DirDotsIx i (dinode image sb i) (dataOf image (dinode image sb i)) :=
  dotsAll_spec image sb ((fsimgValid_iff image sb).mp valid).dots i bound directory

theorem fsimgValid_dirs image sb (valid : fsimgValid image sb = true) : dirsValid image sb = true :=
  ((fsimgValid_iff image sb).mp valid).directories

theorem fsimgValid_links image sb (valid : fsimgValid image sb = true) : linksValid image sb = true :=
  ((fsimgValid_iff image sb).mp valid).links

theorem fsimgValid_link_le image sb z (valid : fsimgValid image sb = true) :
    (linkCount image sb z : Int) ≤ (dinode image sb z).nlinkZ := by
  by_cases inside : 0 < z ∧ z < sb.ninodes
  · exact (linksValid_at image sb z (fsimgValid_links image sb valid) ⟨by omega, inside.2⟩).1
  · rw [linkCount_out image sb z (fsimgValid_dirs image sb valid) inside]
    exact Int.natCast_nonneg _

theorem fsimgValid_link_dir image sb z (valid : fsimgValid image sb = true)
    (directory : (dinode image sb z).typeZ = 1) : linkCount image sb z = 0 := by
  by_cases inside : 0 < z ∧ z < sb.ninodes
  · exact ((linksValid_at image sb z (fsimgValid_links image sb valid) ⟨by omega, inside.2⟩).2 directory).1
  · exact linkCount_out image sb z (fsimgValid_dirs image sb valid) inside

theorem fsimgValid_dir_nlink image sb z (valid : fsimgValid image sb = true)
    (bound : 0 ≤ z ∧ z < sb.ninodes) (directory : (dinode image sb z).typeZ = 1) :
    (dinode image sb z).nlinkZ = 1 :=
  ((linksValid_at image sb z (fsimgValid_links image sb valid) bound).2 directory).2.1

theorem fsimgValid_dir_root image sb z (valid : fsimgValid image sb = true)
    (bound : 0 ≤ z ∧ z < sb.ninodes) (directory : (dinode image sb z).typeZ = 1) : z = 1 :=
  ((linksValid_at image sb z (fsimgValid_links image sb valid) bound).2 directory).2.2

theorem fsimgValid_root_link image sb (valid : fsimgValid image sb = true) :
    linkCount image sb 1 = 0 ∧ (dinode image sb 1).nlinkZ = 1 := by
  have directory := rootValid_type image sb (fsimgValid_root image sb valid)
  have count := (fsimgValid_superblock image sb valid).ninodes
  exact ⟨fsimgValid_link_dir image sb 1 valid directory,
    fsimgValid_dir_nlink image sb 1 valid ⟨by omega, by omega⟩ directory⟩

end Xv6.Fs
