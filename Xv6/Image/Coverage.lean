import Xv6.Image.PackedProofs
import Xv6.Images

/-! Backing-page coverage of the actual generated paper images. These checks
count pages; they do not expand either image into a full byte list. -/
set_option maxRecDepth 4000

namespace Xv6.Image.Coverage

theorem kernel : Images.kernel.Covered := by
  unfold Packed.Covered
  decide

theorem disk : Images.disk.Covered := by
  unfold Packed.Covered
  decide

theorem kernel_lookup (offset : Nat) :
    Images.kernel.getByte? offset = Images.kernel.toBytes[offset]? :=
  Images.kernel.getByte?_eq_lookup kernel offset

theorem disk_lookup (offset : Nat) :
    Images.disk.getByte? offset = Images.disk.toBytes[offset]? :=
  Images.disk.getByte?_eq_lookup disk offset

end Xv6.Image.Coverage
