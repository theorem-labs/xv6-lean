import Xv6.Kernel.KptFetchDefs
import Xv6.Kernel.KptFetchHalfSpec

namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  factor : program = KptFetch.factor KptFetchHalf.program
  unique : ∀ shares, RegisterFootprint.Unique (footprint shares)
  next_two : ∀ pc, is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr (addressAdd pc 2)) 2 = true
  low_cast : ∀ word : BitVec 32, Sail.BitVec.extractLsb word 15 0 = KernelTextDatum.lowHalf word
  halves : ∀ word : BitVec 32, BitVec.append (KernelTextDatum.highHalf word) (KernelTextDatum.lowHalf word) = word

structure ResourceSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  persistent : ∀ era tier pc result, Persistent (instrBytes capacity era tier pc result)
  timeless : ∀ era tier pc result, Timeless (instrBytes capacity era tier pc result)
  partition : ∀ era cpu rs shares,
    iprop(cells capacity era cpu rs shares ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs
        [(.PC,shares.pc),(.misa,shares.misa)] ∗
      KptFetchHalf.cells capacity era cpu rs shares.translation)

/-- Full actual generated fetch from source instruction resources. The
chunk primitive and translation/read programs must be discharged internally.
The only WP input is the guarded continuation after the prescribed result. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  fetch : ∀ shares rs, Config rs → ∀ tier result image fixed whole gen era cpu
    (N : Namespace) root rr continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      instrBytes capacity era tier (rs .PC) result -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root tier result rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post)

end Xv6.Kernel.KptFetch
