import Xv6.Kernel.Sv39MissDefs

namespace Xv6.Kernel.Sv39Miss
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  miss : ∀ shares rs asid path vpn regions, Config rs path vpn regions →
    ∀ permission a d access, KptLeaf.Supported access → KptLeaf.Allows permission access →
    ∀ mxr doSum image fixed whole gen era cpu bound dq values rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
      slots capacity era path vpn permission (KptLeaf.word path.leaf permission a d) bound dq values -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ cachedA cachedD view2 view1 view0 branch,
        ⌜SupervisorPteAD.BranchFacts (KptLeaf.word path.leaf permission cachedA cachedD)
          (KptLeaf.word path.leaf permission a d) access (SupervisorPteAD.enabled rs) branch⌝ -∗
        SupervisorPteAD.guarded branch iprop(
          resources capacity era cpu rs shares asid path vpn permission
            (KptLeaf.word path.leaf permission cachedA cachedD) (KptLeaf.word path.leaf permission a d)
            bound dq values rr view2 view1 view0 branch -∗
          MemoryReadWP.threadWP capacity image fixed whole
            (.hart gen cpu (continuation (result path.leaf branch))) post)) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program asid path vpn access mxr doSum >>= continuation)) post)

end Xv6.Kernel.Sv39Miss
