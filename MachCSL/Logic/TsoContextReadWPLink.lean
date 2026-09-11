import MachCSL.Logic.TsoContextReadWPProofs
import MachCSL.Logic.TsoContextWordLink

namespace MachCSL.Logic.TsoContextReadWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

theorem context_capacity_same {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF) :
    contextCapacity capacity = TsoContext.ofEraCapacity capacity.era := rfl
theorem context_names_same (era : Era.Record) : contextNames era = TsoContext.ofEraNames era := rfl

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem nativeSpec : Spec capacity := actual capacity

/-- The actual explicit normal access kind is a specialization of the general
nonexclusive event theorem, with all remaining request metadata unchanged. -/
theorem wp_read_normal image fixed whole gen era cpu ξ (req : MemoryReadWP.ReadRequest 8)
    (k : MemoryReadWP.ReadResult 8 → SailM Unit) dq (word : BitVec 64) post
    (ram : deviceAddress req.pa = false)
    (normal : req.access_kind = .AK_explicit { variety := .AV_plain, strength := .AS_normal }) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa dq word -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.readMem 8 req) k)) post) :=
  wp_read capacity image fixed whole gen era cpu ξ req k dq word post ram (by rw [normal]; rfl)

/-- Definitional bridge for the emitted V1 builtin; no event is skipped. -/
theorem wp_read_builtin image fixed whole gen era cpu ξ (req : MemoryReadWP.ReadRequest 8)
    (k : MemoryReadWP.ReadResult 8 → SailM Unit) dq (word : BitVec 64) post
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa dq word -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (_root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.sail_mem_read req >>= k)) post) := by
  exact wp_read capacity image fixed whole gen era cpu ξ req k dq word post ram plain

/-- Ordinary reads frame the same reservation fragment; no exclusive-read
snapshot creation or clearing rule is invoked. -/
theorem wp_read_reservation image fixed whole gen era cpu ξ (req : MemoryReadWP.ReadRequest 8)
    (k : MemoryReadWP.ReadResult 8 → SailM Unit) dq (word : BitVec 64) rr post
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa dq word -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.readMem 8 req) k)) post) := by
  iintro Hcert Hrun Hword Hresv Hcontinue
  iapply wp_read capacity image fixed whole gen era cpu ξ req k dq word post ram plain $$ Hcert Hrun Hword
  iintro !> %view Hrun Hword Hreceipt
  iapply Hcontinue $$ Hrun Hword Hresv Hreceipt

end MachCSL.Logic.TsoContextReadWP
