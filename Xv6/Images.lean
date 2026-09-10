import Xv6.Image.Hex
import Xv6.Generated.KernelElf
import Xv6.Generated.FsImg
import Xv6.Generated.KernelElfPacked
import Xv6.Generated.FsImgPacked

namespace Xv6.Images

/-- Canonical representation for efficient kernel-checked byte access. -/
abbrev kernel := Generated.kernelElfPacked

/-- Initial disk representation; reboot must retain live durable state. -/
abbrev disk := Generated.fsImgPacked

/-- Exact paper artifact input. ELF validity and loaded memory are not asserted here. -/
def kernelElf : Option ByteArray := Image.decodeChunks Generated.kernelElfHexChunks

/-- Initial disk only: the machine's reboot transition must retain its durable disk. -/
def initialDisk : Option ByteArray := Image.decodeChunks Generated.fsImgHexChunks

end Xv6.Images
