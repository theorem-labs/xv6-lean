import MachCSL.Logic.SupervisorPteADDefs

namespace MachCSL.Logic.SupervisorPteAD
open Iris Iris.BI MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions
open Xv6.Kernel

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  update : ∀ shares rs address region, Config rs address region →
    ∀ (ppn : BitVec 44) permission a d cachedA cachedD vpn access,
    KptLeaf.Supported access → KptLeaf.Allows permission access → ∀ mxr doSum,
    ∀ image fixed whole gen era cpu bound rr (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte (KptLeaf.word ppn permission a d))
        bound (PteCanonical.slotSet (KptLeaf.word ppn permission false false)) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares address
        (KptLeaf.word ppn permission cachedA cachedD) (KptLeaf.word ppn permission a d)
        (KptLeaf.word ppn permission false false) bound rr access continuation post -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (program vpn address (KptLeaf.word ppn permission cachedA cachedD)
          access mxr doSum >>= continuation)) post)

end MachCSL.Logic.SupervisorPteAD
