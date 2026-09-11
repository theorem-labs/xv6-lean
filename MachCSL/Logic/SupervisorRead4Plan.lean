import MachCSL.Logic.SupervisorRead4Spec
import MachCSL.Logic.SupervisorFetchReadPlan
import MachCSL.Logic.SupervisorDataPmaLink

namespace MachCSL.Logic.SupervisorRead4
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
open SupervisorFetchRead

private theorem returns_bind {fp : RegisterFootprint.Footprint}
    {rs : RegisterFile} {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint)
    (rs : RegisterFile) (value : α) : RegisterPlan.Returns fp rs (pure value) value rs :=
  .pure ⟨rfl, rfl⟩

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact returns_bind plan (pure_plan fp rs _)

private theorem prefix_except {fp rs address n} {segment : SailME ε β} {value : β}
    {next : β → SailME ε α} {result}
    (before : RegisterPlan.Returns fp rs segment.run (.ok value) rs)
    (after : OneRead fp rs address n (next value).run result) :
    OneRead fp rs address n (segment >>= next).run result :=
  OneRead.prefix before after

private theorem one_lift {fp rs address n} {program : SailM α} {value}
    (before : OneRead fp rs address n program value) (ε : Type) :
    OneRead fp rs address n (monadLift program : SailME ε α).run (fun word => Except.ok (value word)) :=
  before.bind (fun v => pure (Except.ok v)) _ (fun _ => rfl)

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
set_option maxHeartbeats 100000 in
theorem checked_boundary (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 4) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (.Load .Data))
    (aligned : is_aligned_paddr (.Physaddr address) 4 = true) :
    OneRead (footprint shares) rs address 4 (program address) (fun word => .Ok (word, ())) := by
  let fp := footprint shares
  have hpma := SupervisorDataPma.priority_plan rs shares.pma
    (show (.pma_regions, shares.pma) ∈ fp by simp [fp, SupervisorFetchRead.footprint]) .load address 4
    region matched grant aligned
  have hpmp : RegisterPlan.Returns fp rs
      (pmpCheck (.Physaddr address) 4 (.Load .Data) .Supervisor) none rs := by
    apply widen (Logic.SupervisorPmp.check_ram_plan (shares.cfg, shares.addr) rs config
      address 4 range.1 range.2.1 range.2.2 (.Load .Data) .load)
    intro cell member
    simp only [Logic.SupervisorPmp.footprint, List.mem_cons, List.not_mem_nil, _root_.or_false] at member
    rcases member with rfl | rfl <;> simp [fp, SupervisorFetchRead.footprint]
  have hmmio := SupervisorPhysical.mmio_ram_plan rs shares.htif
    (show (.htif_tohost_base, shares.htif) ∈ fp by simp [fp, SupervisorFetchRead.footprint]) disabled address 4 range
  have hread := read_ram_boundary fp rs address 4
  unfold program checked_mem_read _root_.Sail.SailME.run PreSail.PreSailME.run
  apply OneRead.bind (value := fun word => (Except.ok (.Ok (word, ())) : Except (Result) (Result)))
  · apply prefix_except (value := SupervisorPhysical.alignedInfo)
    · refine returns_bind (lift_except hpma _) ?_
      exact pure_plan fp rs _
    apply prefix_except (value := ((1, 4) : Int × Int)) (pure_plan fp rs _)
    apply prefix_except (value := read_kind.Read_plain) (lift_except (pure_plan fp rs _) _)
    apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except (Result) (BitVec 32 × Bool × Nat)))
    · simp only [untilFuelM]
      apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except (Result) (BitVec 32 × Bool × Nat)))
      · apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except (Result) (BitVec 32 × Bool × Nat)))
        · apply prefix_except (value := ()) (pure_plan fp rs _)
          dsimp only
          simp only [bits_of_physaddr, Int.toNat, Int.ofNat_zero, Int.zero_mul]
          simp only [add_zero]
          refine OneRead.prefix (lift_except hpmp _) ?_
          refine OneRead.prefix (lift_except hmmio _) ?_
          simp only [ExceptT.bindCont]
          apply OneRead.bind (value := fun word => (Except.ok word : Except (Result) (BitVec 32)))
          · apply OneRead.bind (one_lift hread (Result))
            intro word
            rfl
          · intro word
            change (pure (Except.ok (Sail.BitVec.updateSubrange (0#32) 31 0 word, true, (0 : Nat))) :
              SailM (Except (Result) (BitVec 32 × Bool × Nat))) = _
            rw [full_word]
            rfl
        · intro word; rfl
      · intro word; rfl
    · intro word; rfl
  · intro word; rfl

end MachCSL.Logic.SupervisorRead4
