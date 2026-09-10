import Xv6.Images

/-! Checked facts about the paper's literal images. These establish input bytes,
not ELF loader correctness, filesystem validity, or kernel execution safety. -/
set_option maxRecDepth 4000
set_option maxHeartbeats 400000

namespace Xv6.Image.Facts

/-- The complete 64-byte ELF header of the paper kernel. -/
theorem kernel_header : Images.kernel.readBytes? 0 64 =
    some (ByteArray.mk #[127, 69, 76, 70, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 243, 0, 1, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 56, 86, 4, 0, 0, 0, 0, 0, 5, 0, 0, 0, 64, 0, 56, 0, 3, 0, 64, 0, 21, 0, 20, 0]) := by decide

/-- The superblock bytes used by the filesystem initialization proof. -/
theorem disk_superblock : Images.disk.readBytes? 1024 32 =
    some (ByteArray.mk #[64, 48, 32, 16, 208, 7, 0, 0, 161, 7, 0, 0, 200, 0, 0, 0, 31, 0, 0, 0, 2, 0, 0, 0, 33, 0, 0, 0, 46, 0, 0, 0]) := by decide

/-- Exact input lengths exclude any page padding. -/
theorem input_lengths : Images.kernel.byteLength = 285560 ∧
    Images.disk.byteLength = 2048000 := by decide

/-- Kernel accesses beyond the supplied ELF are rejected. -/
theorem kernel_end : Images.kernel.getByte? 285560 = none := by decide

/-- Disk accesses beyond fs.img are rejected. -/
theorem disk_end : Images.disk.getByte? 2048000 = none := by decide

end Xv6.Image.Facts
