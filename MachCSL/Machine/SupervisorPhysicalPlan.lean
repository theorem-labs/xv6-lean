import MachCSL.Machine.SupervisorPhysicalProofs
import MachCSL.Logic.RegisterPlanProofs
import MachCSL.Logic.SupervisorPmpProofs

namespace MachCSL.Machine.SupervisorPhysical
open LeanPaperStock.Functions MachCSL.Logic MachCSL.Logic.RegisterPlan Iris
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem returns_bind {footprint : RegisterFootprint.Footprint}
    {rs middle after : RegisterFile} {program : SailM α} {next : α → SailM β}
    {value : α} {result : β}
    (first : Returns footprint rs program value middle)
    (rest : Returns footprint middle (next value) result after) :
    Returns footprint rs (program >>= next) result after :=
  Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (footprint : RegisterFootprint.Footprint)
    (rs : RegisterFile) (value : α) : Returns footprint rs (pure value) value rs :=
  .pure ⟨rfl, rfl⟩

private theorem read_plan {footprint : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r, dq) ∈ footprint) :
    Returns footprint rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl, rfl⟩)

private theorem lift_except {footprint : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : Returns footprint rs program value rs) (ε : Type) :
    Returns footprint rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change Returns footprint rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact returns_bind plan (pure_plan footprint rs _)

private theorem except_bind {footprint : RegisterFootprint.Footprint} {program : SailME ε α}
    {next : α → SailME ε β} {rs : RegisterFile} {a : α} {b : Except ε β}
    (first : Returns footprint rs program.run (.ok a) rs)
    (second : Returns footprint rs (next a).run b rs) :
    Returns footprint rs (program >>= next).run b rs := returns_bind first second

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem pma_aligned_plan {footprint : RegisterFootprint.Footprint} (rs : RegisterFile)
    (dq : DFrac) (member : (.pma_regions, dq) ∈ footprint)
    (address : BitVec 64) (n : Nat) (access : MemoryAccessType mem_payload) (reserved : Bool)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (supported : SupportedRead access n reserved)
    (grant : ReadGrant (override_PMA region.attributes .PBMT_PMA) access)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    Returns footprint rs (pmaCheck (.Physaddr address) n access .PBMT_PMA reserved)
      (.Ok alignedInfo) rs := by
  unfold pmaCheck _root_.Sail.SailME.run PreSail.PreSailME.run
  refine returns_bind (value := Except.ok (.Ok alignedInfo)) ?_ (pure_plan footprint rs _)
  refine except_bind (a := override_PMA region.attributes .PBMT_PMA) ?_ ?_
  · refine except_bind (lift_except (read_plan rs .pma_regions dq member) _) ?_
    rw [matched]
    exact pure_plan footprint rs _
  cases supported <;> simp only [ReadGrant] at grant
  all_goals
    refine except_bind (a := true) ?_ ?_
    · rw [grant]
      exact pure_plan footprint rs _
    · simp only [LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine except_bind (lift_except (value := .Ok (.CannotSplit, 0)) ?_ _) ?_
      · unfold mag_pma_check is_mag_applicable_access
        refine returns_bind (pure_plan footprint rs _) ?_
        simp only [aligned, Bool.true_or, ↓reduceIte]
        exact pure_plan footprint rs _
      · exact pure_plan footprint rs _

/-- The successful PMA priority wrapper performs no PMP read. -/
theorem priority_aligned_plan {footprint : RegisterFootprint.Footprint} (rs : RegisterFile)
    (dq : DFrac) (member : (.pma_regions, dq) ∈ footprint)
    (address : BitVec 64) (n : Nat) (access : MemoryAccessType mem_payload) (reserved : Bool)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (supported : SupportedRead access n reserved)
    (grant : ReadGrant (override_PMA region.attributes .PBMT_PMA) access)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    Returns footprint rs
      (check_pma_with_pmp_priority access .PBMT_PMA .Supervisor (.Physaddr address) n reserved)
      (.Ok alignedInfo) rs := by
  unfold check_pma_with_pmp_priority
  exact returns_bind (pma_aligned_plan rs dq member address n access reserved region
    matched supported grant aligned) (pure_plan footprint rs _)

/-- Even on the disabled-HTIF branch the model reads the HTIF register. -/
theorem htif_none_plan {footprint : RegisterFootprint.Footprint} (rs : RegisterFile)
    (dq : DFrac) (member : (.htif_tohost_base, dq) ∈ footprint)
    (disabled : rs .htif_tohost_base = none) (address : BitVec 64) (n : Nat) :
    Returns footprint rs (within_htif_readable (.Physaddr address) n) false rs := by
  unfold within_htif_readable within_htif_writable
  refine returns_bind (read_plan rs .htif_tohost_base dq member) ?_
  rw [disabled]
  exact pure_plan footprint rs _

/-- Exact eager CLINT/signature/HTIF evaluation, with one owned register read. -/
theorem mmio_ram_plan {footprint : RegisterFootprint.Footprint} (rs : RegisterFile)
    (dq : DFrac) (member : (.htif_tohost_base, dq) ∈ footprint)
    (disabled : rs .htif_tohost_base = none) (address : BitVec 64) (n : Nat)
    (range : RamRange address n) :
    Returns footprint rs (within_mmio_readable (.Physaddr address) n) false rs := by
  unfold within_mmio_readable
  simp only [show get_config_rvfi () = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [clint_ram address n range, sig_ram address n]
  refine returns_bind (pure_plan footprint rs false) ?_
  refine returns_bind (pure_plan footprint rs false) ?_
  refine returns_bind (htif_none_plan rs dq member disabled address n) ?_
  exact pure_plan footprint rs _

/-- Useful exact source footprints; every supplied fraction remains explicit. -/
theorem pma_singleton_plan (rs : RegisterFile) (dq : DFrac)
    (address : BitVec 64) (n : Nat) (access : MemoryAccessType mem_payload) (reserved : Bool)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (supported : SupportedRead access n reserved)
    (grant : ReadGrant (override_PMA region.attributes .PBMT_PMA) access)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    Returns [(.pma_regions, dq)] rs
      (pmaCheck (.Physaddr address) n access .PBMT_PMA reserved) (.Ok alignedInfo) rs :=
  pma_aligned_plan rs dq (by simp) address n access reserved region matched supported grant aligned

theorem mmio_singleton_plan (rs : RegisterFile) (dq : DFrac)
    (disabled : rs .htif_tohost_base = none) (address : BitVec 64) (n : Nat)
    (range : RamRange address n) :
    Returns [(.htif_tohost_base, dq)] rs
      (within_mmio_readable (.Physaddr address) n) false rs :=
  mmio_ram_plan rs dq (by simp) disabled address n range

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : Plan small rs program Q) (members : ∀ cell, cell ∈ small → cell ∈ large) :
    Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

/-- Actual PMP-then-PMA API. This returns access information, not a RAM word.
The separate checked-memory-read API uses the priority wrapper first instead. -/
theorem physical_check_plan {footprint : RegisterFootprint.Footprint} (rs : RegisterFile)
    (pmaShare cfgShare addrShare : DFrac)
    (pmaMember : (.pma_regions, pmaShare) ∈ footprint)
    (cfgMember : (.pmpcfg_n, cfgShare) ∈ footprint)
    (addrMember : (.pmpaddr_n, addrShare) ∈ footprint)
    (config : Machine.SupervisorPmp.TorRam rs)
    (address : BitVec 64) (n : Nat) (range : RamRange address n)
    (access : MemoryAccessType mem_payload) (reserved : Bool) (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (supported : SupportedRead access n reserved)
    (grant : ReadGrant (override_PMA region.attributes .PBMT_PMA) access)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    Returns footprint rs
      (phys_access_check access .PBMT_PMA .Supervisor (.Physaddr address) n reserved)
      (.Ok alignedInfo) rs := by
  have pmp := Logic.SupervisorPmp.check_ram_plan (cfgShare, addrShare) rs config
    address n range.1 range.2.1 range.2.2 access (supported_pmp supported)
  have pmp' : Returns footprint rs
      (pmpCheck (.Physaddr address) n access .Supervisor) none rs := by
    apply widen pmp
    intro cell member
    simp only [Logic.SupervisorPmp.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact cfgMember
    · exact addrMember
  unfold phys_access_check
  refine returns_bind pmp' ?_
  exact pma_aligned_plan rs pmaShare pmaMember address n access reserved region
    matched supported grant aligned

end MachCSL.Machine.SupervisorPhysical
