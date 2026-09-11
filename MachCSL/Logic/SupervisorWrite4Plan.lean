import MachCSL.Logic.SupervisorWrite4Defs
import MachCSL.Machine.SupervisorPhysicalPlan
import MachCSL.Logic.SupervisorPmpProofs
import MachCSL.Logic.EventPlanCombinators
import MachCSL.Logic.SupervisorDataPmaLink

namespace MachCSL.Logic.SupervisorWrite4
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

/-- Exact writable MMIO check, including the eager HTIF read and width test. -/
theorem mmio_store_plan {fp : RegisterFootprint.Footprint} (rs : RegisterFile)
    (dq : DFrac) (member : (.htif_tohost_base, dq) ∈ fp)
    (disabled : rs .htif_tohost_base = none) (address : BitVec 64)
    (range : SupervisorPhysical.RamRange address 4) :
    RegisterPlan.Returns fp rs (within_mmio_writable (.Physaddr address) 4) false rs := by
  unfold within_mmio_writable
  simp only [show get_config_rvfi () = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [SupervisorPhysical.clint_ram address 4 range, SupervisorPhysical.sig_ram address 4]
  refine returns_bind (pure_plan fp rs false) ?_
  refine returns_bind (pure_plan fp rs false) ?_
  refine returns_bind (SupervisorPhysical.htif_none_plan rs dq member disabled address 4) ?_
  exact pure_plan fp rs _

theorem Boundary.bind {fp rs req} {program : SailM α} {tail}
    (before : Boundary fp rs req program tail) (next : α → SailM β) :
    Boundary fp rs req (program >>= next) (fun response => tail response >>= next) := by
  induction before with
  | event => exact .event
  | «prefix» first _ ih =>
    rw [BootPmp.sail_bind_assoc]
    exact .prefix first ih

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
    (address : BitVec 64) (word : BitVec 32) :
    OneWrite fp rs address word (write_ram .Write_plain (.Physaddr address) 4 word ()) id := by
  refine ⟨_, .event, ?_, ?_⟩
  · intro result; rfl
  · rfl

theorem add_zero {width : Nat} (address : BitVec width) : Sail.BitVec.addInt address 0 = address := by
  simp [Sail.BitVec.addInt]

theorem full_word (word : BitVec 32) : Sail.BitVec.extractLsb word 31 0 = word := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem checked_boundary (shares : Shares) (rs : RegisterFile) (address : BitVec 64) (word : BitVec 32)
    (config : Machine.SupervisorPmp.TorRam rs) (range : SupervisorPhysical.RamRange address 4)
    (disabled : rs .htif_tohost_base = none) (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (aligned : is_aligned_paddr (.Physaddr address) 4 = true) :
    OneWrite (footprint shares) rs address word (program address word) (fun b => .Ok b) := by
  let fp := footprint shares
  have hpma := SupervisorDataPma.priority_plan rs shares.pma
    (show (.pma_regions, shares.pma) ∈ fp by simp [fp, footprint]) .store address 4 region matched grant aligned
  have hpmp : RegisterPlan.Returns fp rs
      (pmpCheck (.Physaddr address) 4 (.Store .Data) .Supervisor) none rs := by
    apply widen (Logic.SupervisorPmp.check_ram_plan (shares.cfg, shares.addr) rs config
      address 4 range.1 range.2.1 range.2.2 (.Store .Data) .store)
    intro cell member
    simp only [Logic.SupervisorPmp.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [fp, footprint]
  have hmmio := mmio_store_plan rs shares.htif
    (show (.htif_tohost_base, shares.htif) ∈ fp by simp [fp, footprint]) disabled address range
  have hwrite := write_ram_boundary fp rs address word
  unfold program checked_mem_write _root_.Sail.SailME.run PreSail.PreSailME.run
  apply OneWrite.bind (value := fun b => (Except.ok (.Ok b) : Except Result Result))
  · apply prefix_except (value := SupervisorPhysical.alignedInfo)
    · exact returns_bind (lift_except hpma _) (pure_plan fp rs _)
    apply prefix_except (value := ((1, 4) : Int × Int)) (pure_plan fp rs _)
    apply prefix_except (value := write_kind.Write_plain) (lift_except (pure_plan fp rs _) _)
    apply OneWrite.bind (value := fun b => (Except.ok (true, (0 : Nat), b) : Except Result (Bool × Nat × Bool)))
    · simp only [untilFuelM]
      apply OneWrite.bind (value := fun b => (Except.ok (true, (0 : Nat), b) : Except Result (Bool × Nat × Bool)))
      · apply prefix_except (value := ()) (pure_plan fp rs _)
        dsimp only
        simp only [bits_of_physaddr, Int.toNat, Int.ofNat_zero, Int.zero_mul, add_zero]
        refine OneWrite.prefix (lift_except hpmp _) ?_
        apply OneWrite.bind (value := fun b => (Except.ok b : Except Result Bool))
        · refine OneWrite.prefix (lift_except hmmio _) ?_
          simp only [ExceptT.bindCont, Bool.false_eq_true, ↓reduceIte]
          change OneWrite fp rs address word
            (((monadLift (write_ram .Write_plain (.Physaddr address) 4
                (Sail.BitVec.extractLsb word 31 0) ()) : SailME Result Bool) >>= fun value =>
                  pure (true && value)).run) _
          rw [full_word]
          apply OneWrite.bind (one_lift hwrite Result)
          intro b; rfl
        · intro b; rfl
      · intro b; rfl
    · intro b; rfl
  · intro b; rfl

/-- These actual explicit-privilege wrappers add only pure metadata/callbacks.
The effective-privilege/register prefix of `mem_write_value` is not erased. -/
theorem value_priv_meta_eq (address : BitVec 64) (word : BitVec 32) :
    mem_write_value_priv_meta (.Physaddr address) 4 word (.Store .Data)
      .PBMT_PMA .Supervisor () false false false = program address word := by
  unfold mem_write_value_priv_meta program
  change (checked_mem_write (.Physaddr address) 4 word (.Store .Data)
    .PBMT_PMA .Supervisor () false false false >>= Pure.pure) = _
  exact EventPlan.sail_bind_pure_eq _

theorem value_priv_eq (address : BitVec 64) (word : BitVec 32) :
    mem_write_value_priv (.Physaddr address) 4 word .Supervisor (.Store .Data)
      .PBMT_PMA false false false = program address word := by
  exact value_priv_meta_eq address word

end MachCSL.Logic.SupervisorWrite4
