import Xv6.Kernel.KptMemorySpec
import Xv6.Kernel.KptAddressGeometry
import Xv6.Kernel.KernelDatumProofs
import MachCSL.Logic.SupervisorAddressPlan

namespace Xv6.Kernel.KptMemory
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

theorem widen_plan {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

theorem transform_config rs data root (ambient : Ambient rs)
    (rooted : KptResidue.SatpRooted root data.satp) :
    SupervisorAddress.Config (KptAddress.prepare rs data) .Sv39 where
  privilege := by simpa using ambient.address.privilege
  mprv := by simpa using ambient.mprv
  mxr := by simpa using ambient.mxr
  pmm := by simpa using ambient.pmm
  sxl := by simpa using ambient.address.sxl
  decoded := by simp only [KptAddress.prepare_satp, rooted.1]; rfl

theorem transform shares rs data root (ambient : Ambient rs)
    (rooted : KptResidue.SatpRooted root data.satp) va kind :
    RegisterPlan.Returns (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (SupervisorAddress.program va kind) (.Virtaddr va) (KptAddress.prepare rs data) := by
  apply widen_plan (SupervisorAddress.program_plan (transformShares shares) _ .Sv39
    (transform_config rs data root ambient rooted) va kind)
  intro cell member
  simp only [SupervisorAddress.footprint, transformShares, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [KptAddress.footprint, KptAddress.outerShares, KptAddress.innerShares,
      Sv39Address.footprint, SupervisorBare.footprint, KptTranslate.footprint,
      KptMiss.footprint, KptAD.footprint, SupervisorPteAD.footprint]

theorem enabled rs data (ambient : Ambient rs) : KptAD.enabled (KptAddress.prepare rs data) = true := by
  simp [KptAD.enabled, SupervisorPteAD.enabled, ambient.adue]

theorem completed rs data root kind va ppn outcome (ambient : Ambient rs)
    (positive : KernelDatum.Positive va)
    (facts : KptAddress.OutcomeFacts rs data root va ppn .rw (access kind) outcome) :
    CompletedFacts rs data root kind va ppn outcome := by
  refine ⟨facts, ?_⟩
  cases outcome with
  | noncanonical => exact False.elim (facts (KernelDatum.canonical va positive))
  | translated tree p2 p1 a d branch =>
    have enabled := enabled rs data ambient
    have update := facts.2.2.2
    cases branch with
    | hit ca cd branch =>
      cases branch <;> simp_all [KptAddress.result, KptTranslate.result, KptMiss.result,
        Sv39Address.resumed, KptTranslate.Branch.update, KptAD.BranchFacts,
        Sv39Address.physical, KernelDatum.physical]
    | miss ca cd v2 v1 v0 branch =>
      cases branch <;> simp_all [KptAddress.result, KptTranslate.result, KptMiss.result,
        Sv39Address.resumed, KptTranslate.Branch.update, KptAD.BranchFacts,
        Sv39Address.physical, KernelDatum.physical]

theorem read_address_error va error ext : readAfterAddress va (.Err (error,ext)) =
    (memory_exception (.Virtaddr va) error >>= fun failure => pure (.Err failure)) := rfl

theorem read_memory_error va pa excPa error : readAfterMemory va pa (.Err (excPa,error)) =
    (memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error >>= fun failure => pure (.Err failure)) := rfl

theorem write_address_error [Platform] va new error ext : writeAfterAddress va new (.Err (error,ext)) =
    (memory_exception (.Virtaddr va) error >>= fun failure => pure (.Err failure)) := rfl

theorem write_ea_error [Platform] va new pa pbmt excPa error : writeAfterEA va new pa pbmt (.Err (excPa,error)) =
    (memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error >>= fun failure => pure (.Err failure)) := rfl

theorem write_memory_error va pa excPa error : writeAfterMemory va pa (.Err (excPa,error)) =
    (memory_exception (offset_virtaddr_by (.Virtaddr va) pa excPa) error >>= fun failure => pure (.Err failure)) := rfl

theorem write_false va pa : writeAfterMemory va pa (.Ok false) = pure (.Ok false) := rfl

theorem program_factor [Platform] kind va new : program kind va new =
    (SupervisorAddress.program va kind >>= fun address => addressProgram kind (bits_of_virtaddr address) new) := by
  cases kind <;> unfold program SupervisorAddress.program
  all_goals
    apply congrArg (fun next => transform_effective_address (.Virtaddr va) _ >>= next)
    funext address
    cases address
    rfl

end Xv6.Kernel.KptMemory
