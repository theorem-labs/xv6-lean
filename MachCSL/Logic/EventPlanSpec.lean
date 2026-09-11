import MachCSL.Logic.EventPlanDefs
import MachCSL.Logic.RegisterWPSpec
import MachCSL.Logic.MemoryReadWPSpec
import MachCSL.Logic.MemoryExclusiveWPSpec
import MachCSL.Logic.MemoryWriteWPSpec
import MachCSL.Logic.BarrierWPSpec

namespace MachCSL.Logic.EventPlan
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure Contracts {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  registers : RegisterWP.RegisterWPSpec capacity
  plain : MemoryReadWP.MemoryReadWPSpec capacity
  exclusive : MemoryExclusiveWP.MemoryExclusiveWPSpec capacity
  write : MemoryWriteWP.MemoryWriteWPSpec capacity
  barrier : BarrierWP.BarrierWPSpec capacity

/-- This contract is not an inhabitant or an implementation. Its fold must
prove the resource callbacks cover every actual event result. -/
structure EventPlanSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  prefixBind : ∀ {A : Type} reads dq code era (_codeAccess : EventWP.RamAccess capacity era reads dq code)
      image fixed whole gen cpu rs (program : SailM A) Q (continuation : A → SailM Unit) post,
    EventWP.ExecPlan reads rs program Q →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗ code -∗
      (∀ value after, ⌜Q value after⌝ -∗
        EventWP.ownedCells capacity.era.registers (era.registers cpu) after -∗ code -∗
        DeadThread.threadWP capacity image fixed whole (.hart gen cpu (continuation value)) post) -∗
      DeadThread.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post)
  fold : ∀ {S A : Type} reads (rel : Relations S) (R : S → IProp GF) dq code era
      (_codeAccess : EventWP.RamAccess capacity era reads dq code)
      image fixed whole gen cpu (_access : Access capacity fixed gen era cpu rel R)
      rs rr s (program : SailM A) Q (continuation : A → SailM Unit) post,
    Plan reads rel rs rr s program Q →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      EventWP.ownedCells capacity.era.registers (era.registers cpu) rs -∗ code -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗ R s -∗
      (∀ value after rr' next, ⌜Q value after rr' next⌝ -∗
        EventWP.ownedCells capacity.era.registers (era.registers cpu) after -∗ code -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr' -∗ R next -∗
        DeadThread.threadWP capacity image fixed whole (.hart gen cpu (continuation value)) post) -∗
      DeadThread.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post)

end MachCSL.Logic.EventPlan
