import MachCSL.Logic.KptGhostDefs

namespace Xv6.Kernel.KptShared
open MachCSL.Machine MachCSL.Logic

/-- Source KptTree.kpt_tree_spec_gen: both map entries and absent VPNs
constrain the inert tree. Physical ownership is a separate conjunct. -/
def TreeSpec (root : PtTree.PPN) (mapping : KptGhost.Map) (tree : PtTree.Tree) : Prop :=
  PtTree.base tree = root ∧ ∀ vpn,
    match mapping[vpn]? with
    | some (ppn, permission) => ∃ p2 p1 a d,
        PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission a d)
    | none => PtTree.Blocks tree vpn

end Xv6.Kernel.KptShared
