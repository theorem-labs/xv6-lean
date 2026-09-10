import Xv6.Image.Hex
import Xv6.Generated.KernelElf
import Xv6.Generated.FsImg

namespace Xv6.Images

/-- Exact paper artifact input. ELF validity and loaded memory are not asserted here. -/
def kernelElf : Option ByteArray := Image.decodeChunks Generated.kernelElfHexChunks

/-- Initial disk only: the machine's reboot transition must retain its durable disk. -/
def initialDisk : Option ByteArray := Image.decodeChunks Generated.fsImgHexChunks

end Xv6.Images
