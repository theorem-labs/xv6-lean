import MachCSL.Logic.SupervisorPteWriteDefs
import MachCSL.Logic.SupervisorWritePlan
import MachCSL.Machine.SupervisorPhysicalPlan
import MachCSL.Logic.SupervisorPmpProofs
import MachCSL.Logic.EventPlanCombinators

namespace MachCSL.Logic.SupervisorPteWrite
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem returns_bind {fp : RegisterFootprint.Footprint}
    {rs : RegisterFile} {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem read_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (r : Register) (dq : DFrac) (member : (r, dq) ∈ fp) :
    RegisterPlan.Returns fp rs (PreSail.readReg r) (rs r) rs := .read member (.pure ⟨rfl, rfl⟩)

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact returns_bind plan (pure_plan fp rs _)

private theorem except_bind {fp : RegisterFootprint.Footprint} {program : SailME ε α}
    {next : α → SailME ε β} {rs : RegisterFile} {a : α} {b : Except ε β}
    (first : RegisterPlan.Returns fp rs program.run (.ok a) rs)
    (second : RegisterPlan.Returns fp rs (next a).run b rs) :
    RegisterPlan.Returns fp rs (program >>= next).run b rs := returns_bind first second

/-- Actual PTE-write PMA grant; its conditional flag does not use the Data-store assertion. -/
theorem pma_store_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (dq : DFrac) (member : (.pma_regions, dq) ∈ fp) (address : BitVec 64) (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).supports_pte_write = true)
    (aligned : is_aligned_paddr (.Physaddr address) 8 = true) :
    RegisterPlan.Returns fp rs (pmaCheck (.Physaddr address) 8 (.Store .PageTableEntry) .PBMT_PMA true)
      (.Ok SupervisorPhysical.alignedInfo) rs := by
  unfold pmaCheck _root_.Sail.SailME.run PreSail.PreSailME.run
  refine returns_bind (value := Except.ok (.Ok SupervisorPhysical.alignedInfo)) ?_ (pure_plan fp rs _)
  refine except_bind (a := override_PMA region.attributes .PBMT_PMA) ?_ ?_
  · refine except_bind (lift_except (read_plan rs .pma_regions dq member) _) ?_
    rw [matched]
    exact pure_plan fp rs _
  refine except_bind (a := true) ?_ ?_
  · rw [grant]
    exact pure_plan fp rs _
  · simp only [LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine except_bind (lift_except (value := .Ok (.CannotSplit, 0)) ?_ _) ?_
    · unfold mag_pma_check is_mag_applicable_access
      refine returns_bind (pure_plan fp rs _) ?_
      simp only [aligned, Bool.true_or, ↓reduceIte]
      exact pure_plan fp rs _
    · exact pure_plan fp rs _

/-- The successful priority wrapper performs PMA before the later loop's PMP. -/
theorem priority_store_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (dq : DFrac) (member : (.pma_regions, dq) ∈ fp) (address : BitVec 64) (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).supports_pte_write = true)
    (aligned : is_aligned_paddr (.Physaddr address) 8 = true) :
    RegisterPlan.Returns fp rs
      (check_pma_with_pmp_priority (.Store .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr address) 8 true)
      (.Ok SupervisorPhysical.alignedInfo) rs := by
  unfold check_pma_with_pmp_priority
  exact returns_bind (pma_store_plan rs dq member address region matched grant aligned) (pure_plan fp rs _)

theorem OneWrite.bind {fp rs address word} {program : SailM α} {value : Bool → α}
    (before : OneWrite fp rs address word program value) (next : α → SailM β)
    (result : Bool → β) (finish : ∀ success, next (value success) = pure (result success)) :
    OneWrite fp rs address word (program >>= next) result := by
  obtain ⟨tail, cut, ok, error⟩ := before
  refine ⟨fun response => tail response >>= next, cut.bind next, ?_, ?_⟩
  · intro result
    change (tail (.Ok result) >>= next) = _
    rw [ok]
    exact finish true
  · change (tail (.Err ()) >>= next) = _
    rw [error]
    exact finish false

theorem OneWrite.prefix {fp rs address word} {segment : SailM β} {value : β}
    {next : β → SailM α} {result}
    (before : RegisterPlan.Returns fp rs segment value rs)
    (after : OneWrite fp rs address word (next value) result) :
    OneWrite fp rs address word (segment >>= next) result := by
  obtain ⟨tail, cut, success, error⟩ := after
  exact ⟨tail, .prefix before cut, success, error⟩

private theorem prefix_except {fp rs address word} {segment : SailME ε β} {value : β}
    {next : β → SailME ε α} {result}
    (before : RegisterPlan.Returns fp rs segment.run (.ok value) rs)
    (after : OneWrite fp rs address word (next value).run result) :
    OneWrite fp rs address word (segment >>= next).run result := OneWrite.prefix before after

private theorem one_lift {fp rs address word} {program : SailM α} {value}
    (before : OneWrite fp rs address word program value) (ε : Type) :
    OneWrite fp rs address word (monadLift program : SailME ε α).run (fun b => Except.ok (value b)) :=
  before.bind (fun v => pure (Except.ok v)) _ (fun _ => rfl)

/-- All optional successful V1 responses map to true; error maps to false. -/
theorem write_ram_boundary (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (address word : BitVec 64) :
    OneWrite fp rs address word (write_ram .Write_RISCV_conditional (.Physaddr address) 8 word ()) id := by
  refine ⟨_, .event, ?_, ?_⟩
  · intro result; rfl
  · rfl

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

/-- An equality of the complete generated PMP trees, for arbitrary privilege,
address and width. PMA and final memory-event labels are not rewritten. -/
theorem pmp_store_pte_eq (address : physaddr) (width : Nat) (priv : Privilege) :
    pmpCheck address width (.Store .PageTableEntry) priv =
      pmpCheck address width (.Store .Data) priv := by
  simp only [pmpCheck, pmpCheckRWX, accessFaultFromAccessType]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem checked_boundary (shares : Shares) (rs : RegisterFile) (address word : BitVec 64)
    (config : Machine.SupervisorPmp.TorRam rs) (range : SupervisorPhysical.RamRange address 8)
    (disabled : rs .htif_tohost_base = none) (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).supports_pte_write = true)
    (aligned : is_aligned_paddr (.Physaddr address) 8 = true) :
    OneWrite (footprint shares) rs address word (checked address word) (fun b => .Ok b) := by
  let fp := footprint shares
  have hpma := priority_store_plan rs shares.pma
    (show (.pma_regions, shares.pma) ∈ fp by simp [fp, SupervisorWrite.footprint]) address region matched grant aligned
  have hpmp : RegisterPlan.Returns fp rs
      (pmpCheck (.Physaddr address) 8 (.Store .PageTableEntry) .Supervisor) none rs := by
    rw [pmp_store_pte_eq]
    apply widen (Logic.SupervisorPmp.check_ram_plan (shares.cfg, shares.addr) rs config
      address 8 range.1 range.2.1 range.2.2 (.Store .Data) .store)
    intro cell member
    simp only [Logic.SupervisorPmp.footprint, List.mem_cons, List.not_mem_nil, _root_.or_false] at member
    rcases member with rfl | rfl <;> simp [fp, SupervisorWrite.footprint]
  have hmmio := SupervisorWrite.mmio_store_plan rs shares.htif
    (show (.htif_tohost_base, shares.htif) ∈ fp by simp [fp, SupervisorWrite.footprint]) disabled address range
  have hwrite := write_ram_boundary fp rs address word
  unfold checked checked_mem_write _root_.Sail.SailME.run PreSail.PreSailME.run
  apply OneWrite.bind (value := fun b => (Except.ok (.Ok b) : Except Result Result))
  · apply prefix_except (value := SupervisorPhysical.alignedInfo)
    · exact returns_bind (lift_except hpma _) (pure_plan fp rs _)
    apply prefix_except (value := ((1, 8) : Int × Int)) (pure_plan fp rs _)
    apply prefix_except (value := write_kind.Write_RISCV_conditional) (lift_except (pure_plan fp rs _) _)
    apply OneWrite.bind (value := fun b => (Except.ok (true, (0 : Nat), b) : Except Result (Bool × Nat × Bool)))
    · simp only [untilFuelM]
      apply OneWrite.bind (value := fun b => (Except.ok (true, (0 : Nat), b) : Except Result (Bool × Nat × Bool)))
      · apply prefix_except (value := ()) (pure_plan fp rs _)
        dsimp only
        simp only [bits_of_physaddr, Int.toNat, Int.ofNat_zero, Int.zero_mul, SupervisorWrite.add_zero]
        refine OneWrite.prefix (lift_except hpmp _) ?_
        apply OneWrite.bind (value := fun b => (Except.ok b : Except Result Bool))
        · refine OneWrite.prefix (lift_except hmmio _) ?_
          simp only [ExceptT.bindCont, Bool.false_eq_true, ↓reduceIte]
          change OneWrite fp rs address word
            (((monadLift (write_ram .Write_RISCV_conditional (.Physaddr address) 8
                (Sail.BitVec.extractLsb word 63 0) ()) : SailME Result Bool) >>= fun value =>
                  pure (true && value)).run) _
          rw [SupervisorWrite.full_word]
          apply OneWrite.bind (one_lift hwrite Result)
          intro b; rfl
        · intro b; rfl
      · intro b; rfl
    · intro b; rfl
  · intro b; rfl

/-- The explicit-privilege value wrapper adds only the actual pure callback;
all conditional flags and PTE access metadata remain in the checked program. -/
theorem program_eq (address word : BitVec 64) : program address word = checked address word := by
  unfold program mem_write_value_priv mem_write_value_priv_meta checked
  change (checked_mem_write (.Physaddr address) 8 word (.Store .PageTableEntry)
    .PBMT_PMA .Supervisor () false false true >>= Pure.pure) = _
  exact EventPlan.sail_bind_pure_eq _

theorem program_boundary (shares : Shares) (rs : RegisterFile) (address word : BitVec 64)
    (region : PMA_Region) (config : Config rs address region) :
    OneWrite (footprint shares) rs address word
      (write_pte_conditional (.Physaddr address) 8 word) (fun b => .Ok b) := by
  change OneWrite (footprint shares) rs address word (program address word) _
  rw [program_eq]
  exact checked_boundary shares rs address word config.tor config.range config.disabled region
    config.matched config.grant config.aligned

end MachCSL.Logic.SupervisorPteWrite
