import MachCSL.Logic.TsoContextWriteWPProofs

namespace MachCSL.Logic.TsoContextWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContextReadWP

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- All native primitives, context capacities and reservation updates are
implemented; this contract needs no caller-supplied resource callback. -/
theorem nativeSpec : Spec capacity := actual capacity

/-- Explicit normal strength/variety, retaining every other request field. -/
theorem wp_write_normal image fixed whole gen era cpu ξ (req : MemoryWriteWP.WriteRequest 8)
    (old new : BitVec 64) (k : MemoryWriteWP.WriteResult → SailM Unit) rr post
    (present : req.value = some new) (ram : deviceAddress req.pa = false)
    (normal : req.access_kind = .AK_explicit { variety := .AV_plain, strength := .AS_normal }) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok none))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.writeMem 8 req) k)) post) :=
  wp_write capacity image fixed whole gen era cpu ξ req old new k rr post present ram
    (by rw [normal]; rfl)

/-- The present-payload builtin emits exactly the proved write event. The
absent-payload pure announcement is not treated as a write. -/
theorem wp_write_builtin image fixed whole gen era cpu ξ (req : MemoryWriteWP.WriteRequest 8)
    (old new : BitVec 64) (k : MemoryWriteWP.WriteResult → SailM Unit) rr post
    (present : req.value = some new) (ram : deviceAddress req.pa = false)
    (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok none))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (_root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.sail_mem_write req >>= k)) post) := by
  have emit : (_root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.sail_mem_write req >>= k : SailM Unit) =
      .impure (.writeMem 8 req) k := by
    unfold _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.sail_mem_write
    rw [present]
    rfl
  rw [emit]
  exact wp_write capacity image fixed whole gen era cpu ξ req old new k rr post present ram plain

end MachCSL.Logic.TsoContextWriteWP
