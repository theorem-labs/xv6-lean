import MachCSL.Logic.SupervisorPteReadDefs
import MachCSL.Logic.SupervisorReadPlan
import MachCSL.Machine.SupervisorPhysicalPlan
import MachCSL.Logic.SupervisorPmpProofs

namespace MachCSL.Logic.SupervisorPteRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

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

theorem OneRead.bind {fp rs reserved address} {program : SailM α} {value : BitVec 64 → α}
    (before : OneRead fp rs reserved address program value) (next : α → SailM β)
    (result : BitVec 64 → β) (finish : ∀ word, next (value word) = pure (result word)) :
    OneRead fp rs reserved address (program >>= next) result := by
  obtain ⟨tail, cut, success, error⟩ := before
  refine ⟨fun response => tail response >>= next, cut.bind next, ?_, ?_⟩
  · intro word tag
    dsimp only
    rw [success]
    exact finish word
  · dsimp only
    rw [error]
    change (Sail.ArchSem.FreeM.impure (.error Sail.Error.Exit)
      (fun x : Empty => (Empty.elim x : SailM α) >>= next) : SailM β) =
      Sail.ArchSem.FreeM.impure (.error Sail.Error.Exit) Empty.elim
    congr 1
    funext impossible
    exact Empty.elim impossible

theorem OneRead.prefix {fp rs reserved address} {segment : SailM β} {value : β}
    {next : β → SailM α} {result}
    (before : RegisterPlan.Returns fp rs segment value rs)
    (after : OneRead fp rs reserved address (next value) result) :
    OneRead fp rs reserved address (segment >>= next) result := by
  obtain ⟨tail, cut, success, error⟩ := after
  exact ⟨tail, .prefix before cut, success, error⟩

private theorem prefix_except {fp rs reserved address} {segment : SailME ε β} {value : β}
    {next : β → SailME ε α} {result}
    (before : RegisterPlan.Returns fp rs segment.run (.ok value) rs)
    (after : OneRead fp rs reserved address (next value).run result) :
    OneRead fp rs reserved address (segment >>= next).run result :=
  OneRead.prefix before after

private theorem one_lift {fp rs reserved address} {program : SailM α} {value}
    (before : OneRead fp rs reserved address program value) (ε : Type) :
    OneRead fp rs reserved address (monadLift program : SailME ε α).run (fun word => Except.ok (value word)) :=
  before.bind (fun v => pure (Except.ok v)) _ (fun _ => rfl)

theorem read_ram_boundary (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (reserved : Bool) (address : BitVec 64) :
    OneRead fp rs reserved address (read_ram (kind reserved) (.Physaddr address) 8 false)
      (fun word => (word, ())) := by
  cases reserved <;> refine ⟨_, .event, ?_, ?_⟩
  all_goals intros; rfl

theorem add_zero {width : Nat} (address : BitVec width) : Sail.BitVec.addInt address 0 = address := by
  simp [Sail.BitVec.addInt]

theorem full_word (old word : BitVec 64) :
    Sail.BitVec.updateSubrange old 63 0 word = word := by
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]

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
theorem checked_boundary (shares : Shares) (rs : RegisterFile) (reserved : Bool)
    (address : BitVec 64) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 8) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (.Load .PageTableEntry))
    (aligned : is_aligned_paddr (.Physaddr address) 8 = true) :
    OneRead (footprint shares) rs reserved address (checked reserved address) (fun word => .Ok (word, ())) := by
  let fp := footprint shares
  have hpma := SupervisorPhysical.priority_aligned_plan rs shares.pma
    (show (.pma_regions, shares.pma) ∈ fp by simp [fp, SupervisorRead.footprint]) address 8 (.Load .PageTableEntry) reserved
    region matched (SupervisorPhysical.SupportedRead.pte reserved) grant aligned
  have hpmp : RegisterPlan.Returns fp rs
      (pmpCheck (.Physaddr address) 8 (.Load .PageTableEntry) .Supervisor) none rs := by
    apply widen (Logic.SupervisorPmp.check_ram_plan (shares.cfg, shares.addr) rs config
      address 8 range.1 range.2.1 range.2.2 (.Load .PageTableEntry) (SupervisorPhysical.supported_pmp (SupervisorPhysical.SupportedRead.pte reserved)))
    intro cell member
    simp only [Logic.SupervisorPmp.footprint, List.mem_cons, List.not_mem_nil, _root_.or_false] at member
    rcases member with rfl | rfl <;> simp [fp, SupervisorRead.footprint]
  have hmmio := SupervisorPhysical.mmio_ram_plan rs shares.htif
    (show (.htif_tohost_base, shares.htif) ∈ fp by simp [fp, SupervisorRead.footprint]) disabled address 8 range
  have hread := read_ram_boundary fp rs reserved address
  have hkind : RegisterPlan.Returns fp rs (read_kind_of_flags false false reserved) (kind reserved) rs := by
    cases reserved <;> exact pure_plan fp rs _
  unfold checked checked_mem_read _root_.Sail.SailME.run PreSail.PreSailME.run
  apply OneRead.bind (value := fun word => (Except.ok (.Ok (word, ())) : Except CheckedResult CheckedResult))
  · apply prefix_except (value := SupervisorPhysical.alignedInfo)
    · refine returns_bind (lift_except hpma _) ?_
      exact pure_plan fp rs _
    apply prefix_except (value := ((1, 8) : Int × Int)) (pure_plan fp rs _)
    apply prefix_except (value := kind reserved) (lift_except hkind _)
    apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except CheckedResult (BitVec 64 × Bool × Nat)))
    · simp only [untilFuelM]
      apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except CheckedResult (BitVec 64 × Bool × Nat)))
      · apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except CheckedResult (BitVec 64 × Bool × Nat)))
        · apply prefix_except (value := ()) (pure_plan fp rs _)
          dsimp only
          simp only [bits_of_physaddr, Int.toNat, Int.ofNat_zero, Int.zero_mul]
          simp only [add_zero]
          refine OneRead.prefix (lift_except hpmp _) ?_
          refine OneRead.prefix (lift_except hmmio _) ?_
          simp only [ExceptT.bindCont]
          apply OneRead.bind (value := fun word => (Except.ok word : Except CheckedResult (BitVec 64)))
          · apply OneRead.bind (one_lift hread CheckedResult)
            intro word
            rfl
          · intro word
            change (pure (Except.ok (Sail.BitVec.updateSubrange (0#64) 63 0 word, true, (0 : Nat))) :
              SailM (Except CheckedResult (BitVec 64 × Bool × Nat))) = _
            rw [full_word]
            rfl
        · intro word; rfl
      · intro word; rfl
    · intro word; rfl
  · intro word; rfl

theorem program_eq (reserved : Bool) (address : BitVec 64) :
    program reserved address =
      (checked reserved address >>= fun value => pure (MemoryOpResult_drop_meta value)) := by
  cases reserved <;>
    simp [program, mem_read_priv, mem_read_priv_meta, checked, BootPmp.sail_bind_assoc,
      BootPmp.sail_pure_bind]

theorem program_boundary (shares : Shares) (rs : RegisterFile) (reserved : Bool)
    (address : BitVec 64) (region : PMA_Region) (config : Config rs address region) :
    OneRead (footprint shares) rs reserved address (program reserved address) (fun word => .Ok word) := by
  rw [program_eq]
  apply OneRead.bind (checked_boundary shares rs reserved address config.tor config.range
    config.disabled region config.matched config.grant config.aligned)
  intro word
  rfl

theorem actual_plain (address : BitVec 64) : program false address = read_pte (.Physaddr address) 8 := rfl
theorem actual_exclusive (address : BitVec 64) :
    program true address = read_pte_exclusive (.Physaddr address) 8 := rfl

end MachCSL.Logic.SupervisorPteRead
