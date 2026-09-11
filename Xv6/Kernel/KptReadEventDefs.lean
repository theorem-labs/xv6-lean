import Xv6.Kernel.KptSharedDefs
import MachCSL.Logic.MemoryReadWPDefs

namespace Xv6.Kernel.KptReadEvent
open MachCSL.Machine MachCSL.Memory

abbrev Capacity := KptShared.Capacity

/-- Exact selected address on a source three-level path. -/
def address (tree : PtTree.Tree) (vpn : PtTree.VPN) (p2 p1 : PtTree.Word)
    (level : Fin 3) : PhysicalAddress :=
  match level.val with
  | 2 => PtTree.addr2 tree vpn
  | 1 => PtTree.addr1 p2 vpn
  | _ => PtTree.addr0 p1 vpn

def reference (p2 p1 p0 : PtTree.Word) (level : Fin 3) : PtTree.Word :=
  match level.val with
  | 2 => p2
  | 1 => p1
  | _ => p0

/-- The leaf may vary in A/D; a nonleaf is read exactly. The word is chosen
inside each permitted view, not once for all machine interleavings. -/
def ReadFact (reference word : PtTree.Word) : Prop :=
  PteCanonical.canon word = PteCanonical.canon reference ∧
    (PteCanonical.nonleaf reference = true → word = reference)

end Xv6.Kernel.KptReadEvent
