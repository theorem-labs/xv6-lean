import Xv6.Kernel.MycpuDecodeDefs

namespace Xv6.Kernel.MycpuFetchBytes
open MachCSL.Memory LeanPaperStock.Functions

/-- Full concrete footprint of the generated Ziccif aligned fetch path.
The final four-byte fetch includes two bytes following the function body. -/
def bytes : List UInt8 := MycpuDecode.bytes ++ [0x01, 0x11]
def width (i : Fin 14) : Nat :=
  if is_aligned_vaddr (.Virtaddr (MycpuDecode.address i)) 4 then 4 else 2

def encoding (i : Fin 14) : Nat :=
  match i.val with
  | 0 => 0x1141
  | 1 => 0xe022e406
  | 2 => 0xe022
  | 3 => 0x87920800
  | 4 => 0x8792
  | 5 => 0x79e2781
  | 6 => 0x79e
  | 7 => 0x11517
  | 8 => 0xb2050513
  | 9 => 0x60a2953e
  | 10 => 0x60a2
  | 11 => 0x1416402
  | 12 => 0x141
  | _ => 0x11018082
def word (i : Fin 14) : BitVec (8 * width i) := BitVec.ofNat _ (encoding i)

end Xv6.Kernel.MycpuFetchBytes
