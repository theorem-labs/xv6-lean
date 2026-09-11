import Xv6.Kernel.KptMemoryDefs

namespace Xv6.Kernel.KptMemory
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec [Platform] : Prop where
  transform : ∀ shares rs data root, Ambient rs → KptResidue.SatpRooted root data.satp →
    ∀ va kind, RegisterPlan.Returns (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (SupervisorAddress.program va kind) (.Virtaddr va) (KptAddress.prepare rs data)
  address : ∀ shares rs data root, Ambient rs → KptResidue.SatpRooted root data.satp →
    ∀ va new kind, TsoContextWord.Aligned va →
    Sv39Address.Boundary (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (KptAddress.program va (access kind)) (addressProgram kind va new) (afterAddress kind va new)
  completed : ∀ rs data root kind va ppn outcome, Ambient rs → KernelDatum.Positive va →
    KptAddress.OutcomeFacts rs data root va ppn .rw (access kind) outcome →
    CompletedFacts rs data root kind va ppn outcome
  read_address_error : ∀ va error ext, readAfterAddress va (.Err (error,ext)) =
    (memory_exception (.Virtaddr va) error >>= fun failure => pure (.Err failure))
  read_memory_error : ∀ va pa excPa error, readAfterMemory va pa (.Err (excPa,error)) =
    (memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error >>= fun failure => pure (.Err failure))
  write_address_error : ∀ va new error ext, writeAfterAddress va new (.Err (error,ext)) =
    (memory_exception (.Virtaddr va) error >>= fun failure => pure (.Err failure))
  write_ea_error : ∀ va new pa pbmt excPa error, writeAfterEA va new pa pbmt (.Err (excPa,error)) =
    (memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error >>= fun failure => pure (.Err failure))
  write_memory_error : ∀ va pa excPa error, writeAfterMemory va pa (.Err (excPa,error)) =
    (memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error >>= fun failure => pure (.Err failure))
  write_false : ∀ va pa, writeAfterMemory va pa (.Ok false) = pure (.Ok false)

/-- Source virtual words and the actual residue pay both translation and
ordinary memory. No current physical word, mapping witness, hardware grant,
per-step callback, successful translation or trap-handler WP is an input. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  address : ∀ shares rs, Ambient rs → ∀ kind tier ξ va dq old new rr,
    (kind = .store → dq = .own 1) →
    ∀ image fixed whole gen era cpu (N : Namespace) root
      (continuation : Result kind → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      auxiliaryCells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ KernelDatum.word capacity era tier ξ va dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root kind tier ξ va dq old new rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (addressProgram kind va new >>= continuation)) post)
  transformed : ∀ shares rs, Ambient rs → ∀ kind tier ξ va dq old new rr,
    (kind = .store → dq = .own 1) →
    ∀ image fixed whole gen era cpu (N : Namespace) root
      (continuation : Result kind → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      auxiliaryCells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ KernelDatum.word capacity era tier ξ va dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares N root kind tier ξ va dq old new rr continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (program kind va new >>= continuation)) post)

end Xv6.Kernel.KptMemory
