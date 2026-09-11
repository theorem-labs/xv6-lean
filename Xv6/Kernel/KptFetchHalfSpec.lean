import Xv6.Kernel.KptFetchHalfDefs

namespace Xv6.Kernel.KptFetchHalf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  factor : ∀ start address n,
    program start address n = KptAddress.program address (.InstructionFetch ()) >>= afterTranslation n
  page : ∀ address n, Supported n → is_aligned_vaddr (.Virtaddr address) n = true →
    KernelTextDatum.SamePage address n
  physical_alignment : ∀ address ppn n, Supported n →
    is_aligned_vaddr (.Virtaddr address) n = true →
    is_aligned_paddr (.Physaddr (KernelTextDatum.physical ppn address)) n = true
  translation_success : ∀ rs root step, Config rs → Step.Facts rs root step →
    KptAddress.result step.address step.ppn (.InstructionFetch ()) step.outcome =
      .Ok (.Physaddr (KernelTextDatum.physical step.ppn step.address), .PBMT_PMA, ())
  physical_read : ∀ shares rs data, Config rs → SupervisorPmp.TorRam (KptAddress.prepare rs data) →
    ∀ address n, Supported n → KernelTextDatum.AddrIsText address →
    is_aligned_paddr (.Physaddr address) n = true →
    SupervisorFetchRead.OneRead (KptAddress.footprint shares) (KptAddress.prepare rs data) address n
      (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr address) n false false false)
      (fun word => .Ok word)

/-- Fully discharged actual translate+physical-read chunk. No supplied
translation WP, successful response, physical word or memory-read oracle. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  fetch : ∀ shares rs, Config rs → ∀ start address n, Supported n →
    is_aligned_vaddr (.Virtaddr address) n = true → ∀ tier (word : BitVec (8*n))
    image fixed whole gen era cpu (N : Namespace) root rr continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      window capacity era tier address n .discard word -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tier address n word rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program start address n >>= continuation)) post)

end Xv6.Kernel.KptFetchHalf
