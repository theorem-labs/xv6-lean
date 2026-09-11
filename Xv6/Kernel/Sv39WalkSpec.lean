import Xv6.Kernel.Sv39WalkDefs

namespace Xv6.Kernel.Sv39Walk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  pointer_flags : ∀ ppn, PteCanonical.flags (pointer ppn) = 1#8
  pointer_ppn : ∀ ppn, PPN_of_PTE (pointer ppn) = ppn
  pointer_ext : ∀ ppn, ext_bits_of_PTE (pointer ppn) = 0#10
  pointer_nonleaf : ∀ ppn, PteCanonical.nonleaf (pointer ppn) = true
  pointer_valid : ∀ rs ppn, RegisterPlan.Returns [] rs
    (pte_is_invalid (PteCanonical.flags (pointer ppn)) (ext_bits_of_PTE (pointer ppn))) false rs
  address_value : ∀ ppn index, (addressAt ppn index).toNat = ppn.toNat * 4096 + index.toNat * 8
  address_aligned : ∀ ppn index, is_aligned_paddr (.Physaddr (addressAt ppn index)) 8 = true
  leaf_variant : ∀ ppn permission word,
    PteCanonical.canon word = PteCanonical.canon (KptLeaf.word ppn permission false false) →
    ∃ a d, word = KptLeaf.word ppn permission a d

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  walk : ∀ shares rs path vpn regions, Config rs path vpn regions →
    ∀ permission access, KptLeaf.Supported access → KptLeaf.Allows permission access →
    ∀ mxr doSum global image fixed whole gen era cpu bound dq values rr
      (continuation : Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.credential capacity era cpu bound -∗
      slots capacity era path vpn permission bound dq values -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ a d view2 view1 view0,
        cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
        slots capacity era path vpn permission bound dq values -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        receipts capacity era cpu view2 view1 view0 -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (output path vpn permission global a d, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program path vpn access mxr doSum global >>= continuation)) post)

end Xv6.Kernel.Sv39Walk
