import Xv6.Kernel.KptJalDefs
import Xv6.Kernel.KernelTextImageDefs
import Xv6.Generated.KernelMapsMetadata

namespace Xv6.Kernel.PushOffMycpuCalls
open Iris MachCSL.Machine MachCSL.Logic
abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Site := Fin 3

def offset (site : Site) : Int := if site.val = 0 then 0x10 else if site.val = 1 then 0x18 else 0x2c
def address (site : Site) : Int := Xv6.Generated.KernelMaps.Symbols.push_off + offset site
def pc (site : Site) : BitVec 64 := KernelTextImage.address (address site)
def immediate (site : Site) : BitVec 21 := if site.val = 0 then 3370#21 else if site.val = 1 then 3362#21 else 3342#21
def encoding (site : Site) : BitVec 32 := if site.val = 0 then 0x52b000ef#32 else if site.val = 1 then 0x523000ef#32 else 0x50f000ef#32

end Xv6.Kernel.PushOffMycpuCalls
