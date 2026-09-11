import MachCSL.Logic.SupervisorFetchReadDefs
import MachCSL.Machine.SupervisorPhysicalPlan
import MachCSL.Logic.SupervisorPmpProofs

namespace MachCSL.Logic.SupervisorFetchRead
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

theorem Boundary.bind {fp rs n} {req : MemoryReadWP.ReadRequest n} {program : SailM α} {tail}
    (before : Boundary fp rs req program tail) (next : α → SailM β) :
    Boundary fp rs req (program >>= next) (fun response => tail response >>= next) := by
  induction before with
  | event => exact .event
  | «prefix» first _ ih =>
    rw [BootPmp.sail_bind_assoc]
    exact .prefix first ih

theorem OneRead.bind {fp rs address n} {program : SailM α} {value : BitVec (8 * n) → α}
    (before : OneRead fp rs address n program value) (next : α → SailM β)
    (result : BitVec (8 * n) → β) (finish : ∀ word, next (value word) = pure (result word)) :
    OneRead fp rs address n (program >>= next) result := by
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

theorem OneRead.prefix {fp rs address n} {segment : SailM β} {value : β}
    {next : β → SailM α} {result}
    (before : RegisterPlan.Returns fp rs segment value rs)
    (after : OneRead fp rs address n (next value) result) :
    OneRead fp rs address n (segment >>= next) result := by
  obtain ⟨tail, cut, success, error⟩ := after
  exact ⟨tail, .prefix before cut, success, error⟩

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

theorem read_ram_boundary (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (address : BitVec 64) (n : Nat) :
    OneRead fp rs address n (read_ram .Read_plain (.Physaddr address) n false)
      (fun word => (word, ())) := by
  refine ⟨_, .event, ?_, ?_⟩
  · intro word tag; rfl
  · rfl

theorem add_zero {width : Nat} (address : BitVec width) : Sail.BitVec.addInt address 0 = address := by
  simp [Sail.BitVec.addInt]

theorem full_halfword (old word : BitVec 16) :
    Sail.BitVec.updateSubrange old 15 0 word = word := by
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]

theorem full_word (old word : BitVec 32) :
    Sail.BitVec.updateSubrange old 31 0 word = word := by
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
private theorem checked_2 (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 2) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 2 = some region)
    (grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (.InstructionFetch ()))
    (aligned : is_aligned_paddr (.Physaddr address) 2 = true) :
    OneRead (footprint shares) rs address 2 (program address 2) (fun word => .Ok (word, ())) := by
  let fp := footprint shares
  have hpma := SupervisorPhysical.priority_aligned_plan rs shares.pma
    (show (.pma_regions, shares.pma) ∈ fp by simp [fp, footprint]) address 2 (.InstructionFetch ()) false
    region matched SupervisorPhysical.SupportedRead.fetch2 grant aligned
  have hpmp : RegisterPlan.Returns fp rs
      (pmpCheck (.Physaddr address) 2 (.InstructionFetch ()) .Supervisor) none rs := by
    apply widen (Logic.SupervisorPmp.check_ram_plan (shares.cfg, shares.addr) rs config
      address 2 range.1 range.2.1 range.2.2 (.InstructionFetch ()) (SupervisorPhysical.supported_pmp SupervisorPhysical.SupportedRead.fetch2))
    intro cell member
    simp only [Logic.SupervisorPmp.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [fp, footprint]
  have hmmio := SupervisorPhysical.mmio_ram_plan rs shares.htif
    (show (.htif_tohost_base, shares.htif) ∈ fp by simp [fp, footprint]) disabled address 2 range
  have hread := read_ram_boundary fp rs address 2
  unfold program checked_mem_read _root_.Sail.SailME.run PreSail.PreSailME.run
  apply OneRead.bind (value := fun word => (Except.ok (.Ok (word, ())) : Except (Result 2) (Result 2)))
  · apply prefix_except (value := SupervisorPhysical.alignedInfo)
    · refine returns_bind (lift_except hpma _) ?_
      exact pure_plan fp rs _
    apply prefix_except (value := ((1, 2) : Int × Int)) (pure_plan fp rs _)
    apply prefix_except (value := read_kind.Read_plain) (lift_except (pure_plan fp rs _) _)
    apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except (Result 2) (BitVec 16 × Bool × Nat)))
    · simp only [untilFuelM]
      apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except (Result 2) (BitVec 16 × Bool × Nat)))
      · apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except (Result 2) (BitVec 16 × Bool × Nat)))
        · apply prefix_except (value := ()) (pure_plan fp rs _)
          dsimp only
          simp only [bits_of_physaddr, Int.toNat, Int.ofNat_zero, Int.zero_mul]
          simp only [add_zero]
          refine OneRead.prefix (lift_except hpmp _) ?_
          refine OneRead.prefix (lift_except hmmio _) ?_
          simp only [ExceptT.bindCont]
          apply OneRead.bind (value := fun word => (Except.ok word : Except (Result 2) (BitVec 16)))
          · apply OneRead.bind (one_lift hread (Result 2))
            intro word
            rfl
          · intro word
            change (pure (Except.ok (Sail.BitVec.updateSubrange (0#16) 15 0 word, true, (0 : Nat))) :
              SailM (Except (Result 2) (BitVec 16 × Bool × Nat))) = _
            rw [full_halfword]
            rfl
        · intro word; rfl
      · intro word; rfl
    · intro word; rfl
  · intro word; rfl


set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000 in
private theorem checked_4 (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 4) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (.InstructionFetch ()))
    (aligned : is_aligned_paddr (.Physaddr address) 4 = true) :
    OneRead (footprint shares) rs address 4 (program address 4) (fun word => .Ok (word, ())) := by
  let fp := footprint shares
  have hpma := SupervisorPhysical.priority_aligned_plan rs shares.pma
    (show (.pma_regions, shares.pma) ∈ fp by simp [fp, footprint]) address 4 (.InstructionFetch ()) false
    region matched SupervisorPhysical.SupportedRead.fetch4 grant aligned
  have hpmp : RegisterPlan.Returns fp rs
      (pmpCheck (.Physaddr address) 4 (.InstructionFetch ()) .Supervisor) none rs := by
    apply widen (Logic.SupervisorPmp.check_ram_plan (shares.cfg, shares.addr) rs config
      address 4 range.1 range.2.1 range.2.2 (.InstructionFetch ()) (SupervisorPhysical.supported_pmp SupervisorPhysical.SupportedRead.fetch4))
    intro cell member
    simp only [Logic.SupervisorPmp.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [fp, footprint]
  have hmmio := SupervisorPhysical.mmio_ram_plan rs shares.htif
    (show (.htif_tohost_base, shares.htif) ∈ fp by simp [fp, footprint]) disabled address 4 range
  have hread := read_ram_boundary fp rs address 4
  unfold program checked_mem_read _root_.Sail.SailME.run PreSail.PreSailME.run
  apply OneRead.bind (value := fun word => (Except.ok (.Ok (word, ())) : Except (Result 4) (Result 4)))
  · apply prefix_except (value := SupervisorPhysical.alignedInfo)
    · refine returns_bind (lift_except hpma _) ?_
      exact pure_plan fp rs _
    apply prefix_except (value := ((1, 4) : Int × Int)) (pure_plan fp rs _)
    apply prefix_except (value := read_kind.Read_plain) (lift_except (pure_plan fp rs _) _)
    apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except (Result 4) (BitVec 32 × Bool × Nat)))
    · simp only [untilFuelM]
      apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except (Result 4) (BitVec 32 × Bool × Nat)))
      · apply OneRead.bind (value := fun word => (Except.ok (word, true, (0 : Nat)) : Except (Result 4) (BitVec 32 × Bool × Nat)))
        · apply prefix_except (value := ()) (pure_plan fp rs _)
          dsimp only
          simp only [bits_of_physaddr, Int.toNat, Int.ofNat_zero, Int.zero_mul]
          simp only [add_zero]
          refine OneRead.prefix (lift_except hpmp _) ?_
          refine OneRead.prefix (lift_except hmmio _) ?_
          simp only [ExceptT.bindCont]
          apply OneRead.bind (value := fun word => (Except.ok word : Except (Result 4) (BitVec 32)))
          · apply OneRead.bind (one_lift hread (Result 4))
            intro word
            rfl
          · intro word
            change (pure (Except.ok (Sail.BitVec.updateSubrange (0#32) 31 0 word, true, (0 : Nat))) :
              SailM (Except (Result 4) (BitVec 32 × Bool × Nat))) = _
            rw [full_word]
            rfl
        · intro word; rfl
      · intro word; rfl
    · intro word; rfl
  · intro word; rfl


theorem checked_boundary (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (n : Nat) (width : Supported n) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address n) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    OneRead (footprint shares) rs address n (program address n) (fun word => .Ok (word, ())) := by
  rcases width with rfl | rfl
  · exact checked_2 shares rs address config range disabled region matched grant aligned
  · exact checked_4 shares rs address config range disabled region matched grant aligned

end MachCSL.Logic.SupervisorFetchRead
