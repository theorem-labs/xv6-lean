import Xv6.Kernel.PushOffWord4BarePure

namespace Xv6.Kernel.PushOffWord4Bare.Write
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions SupervisorWrite4
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem widen_plan {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {Q : α → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

private theorem widen_boundary {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {req : MemoryWriteWP.WriteRequest 4} {program : SailM α} {tail}
    (cut : Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen_plan first members) ih

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {address : BitVec 64} {word : BitVec 32} {program : SailM α} {value}
    (cut : OneWrite small rs address word program value)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : OneWrite large rs address word program value := by
  obtain ⟨tail, cut, success, error⟩ := cut
  exact ⟨tail, widen_boundary cut members, success, error⟩

private theorem returns_bind {fp : RegisterFootprint.Footprint}
    {rs : RegisterFile} {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl, rfl⟩

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact returns_bind plan (pure_plan fp rs _)

private theorem prefix_except {fp rs address word} {segment : SailME ε β} {value : β}
    {next : β → SailME ε α} {result}
    (before : RegisterPlan.Returns fp rs segment.run (.ok value) rs)
    (after : OneWrite fp rs address word (next value).run result) :
    OneWrite fp rs address word (segment >>= next).run result := OneWrite.prefix before after

private theorem one_lift {fp rs address word} {program : SailM α} {value}
    (before : OneWrite fp rs address word program value) (ε : Type) :
    OneWrite fp rs address word (monadLift program : SailME ε α).run (fun word => Except.ok (value word)) := by
  exact OneWrite.bind before _ _ (fun _ => rfl)


theorem effective_plan (shares : Shares) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Supervisor) (clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1) :
    RegisterPlan.Returns (footprint shares) rs
      (SupervisorMemOuter.effective (.Store .Data)) .Supervisor rs := by
  apply widen_plan (SupervisorMemOuter.effective_plan (SupervisorBareFetch.outerShares shares.bare) rs _ priv (Or.inr clear))
  intro cell member
  simp only [SupervisorMemOuter.footprint, SupervisorBareFetch.outerShares, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint]

theorem outer_boundary (shares : Shares) (rs : RegisterFile) (address : BitVec 64) (word : BitVec 32)
    (config : Config rs) (range : SupervisorPhysical.RamRange address 4)
    (aligned : is_aligned_paddr (.Physaddr address) 4 = true) :
    OneWrite (footprint shares) rs address word
      (mem_write_value (.Physaddr address) 4 word (.Store .Data) .PBMT_PMA false false false)
      (fun value => .Ok value) := by
  change OneWrite _ _ _ _ (SupervisorMemOuter4.writeProgram address word) _
  rw [SupervisorMemOuter4.write_factor]
  apply OneWrite.prefix (effective_plan shares rs config.transform.privilege config.transform.mprv)
  rw [SupervisorMemOuter4.write_supervisor]
  apply widen (checked_boundary ⟨shares.bare.physical.pma, shares.bare.physical.cfg, shares.bare.physical.addr, shares.bare.physical.htif⟩ rs address word config.tor range config.htif
    KptHardware.ramRegion (pma rs config address range) (by rfl) aligned)
  intro cell member
  exact List.mem_append_right _ (List.mem_append_right _ member)

theorem ea_plan (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (config : Config rs) (range : SupervisorPhysical.RamRange address 4)
    (aligned : is_aligned_paddr (.Physaddr address) 4 = true) :
    RegisterPlan.Returns (footprint shares) rs
      (mem_write_ea (.Physaddr address) 4 (.Store .Data) .PBMT_PMA false false false) (.Ok ()) rs := by
  apply widen_plan (SupervisorWriteEA4.program_plan
    ⟨shares.bare.translation.status, shares.bare.translation.privilege, shares.bare.physical.pma,
      shares.bare.physical.cfg, shares.bare.physical.addr⟩ rs address KptHardware.ramRegion
    ⟨config.transform.privilege, config.transform.mprv, config.tor, range, (pma rs config address range), (by rfl), aligned⟩)
  intro cell member
  simp only [SupervisorWriteEA.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint, SupervisorFetchRead.footprint]

theorem virtual_boundary [Platform] (shares : Shares) (rs : RegisterFile) (address : BitVec 64) (word : BitVec 32)
    (config : Config rs) (range : SupervisorPhysical.RamRange address 4)
    (aligned : address.toNat % 4 = 0) :
    OneWrite (footprint shares) rs address word (addressProgram .store address word) (fun value => .Ok value) := by
  have physicalAligned : is_aligned_paddr (.Physaddr address) 4 = true := by
    unfold is_aligned_paddr _root_.Sail.BitVec.toNatInt
    change ((Int.tmod (address.toNat : Int) 4) == 0) = true
    change (((address.toNat % 4 : Nat) : Int) == 0) = true
    rw [aligned]; rfl
  have virtualAligned : is_aligned_vaddr (.Virtaddr address) 4 = true := physicalAligned
  have split : RegisterPlan.Returns (footprint shares) rs (split_on_page_boundary address 4) (4, 0) rs := by
    rw [KptMemory4.split_page_four address aligned]
    exact pure_plan _ _ _
  have mode := SupervisorBare.mode_plan rs shares.bare.translation.status shares.bare.translation.satp
    (show (.mstatus, shares.bare.translation.status) ∈ footprint shares by
      simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint])
    (show (.satp, shares.bare.translation.satp) ∈ footprint shares by
      simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint]) config.transform.sxl (bare_config rs config).mode
  have trans : RegisterPlan.Returns (footprint shares) rs
      (translateAddr (.Virtaddr address) (.Store .Data)) (.Ok (.Physaddr address, .PBMT_PMA, ())) rs := by
    apply widen_plan (SupervisorBare.mprv_zero_plan shares.bare.translation rs (bare_config rs config) address _ .store config.transform.mprv)
    intro cell member; exact List.mem_append_right _ (List.mem_append_left _ member)
  have hea := ea_plan shares rs address config range physicalAligned
  have value := outer_boundary shares rs address word config range physicalAligned
  unfold addressProgram KptMemory4.addressProgram vmem_write_addr _root_.Sail.SailME.run PreSail.PreSailME.run
  apply OneWrite.bind (value := fun b => (Except.ok (.Ok b) : Except (Result .store) (Result .store)))
  · simp only [virtualAligned, LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    apply prefix_except (value := ((4, 0) : Int × Int)) (lift_except split (Result .store))
    apply prefix_except (value := rs .mstatus)
      (lift_except (RegisterPlan.Plan.read (dq := shares.bare.translation.status)
        (by simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint]) (.pure ⟨rfl, rfl⟩)) (Result .store))
    apply prefix_except (value := rs .cur_privilege)
      (lift_except (RegisterPlan.Plan.read (dq := shares.bare.translation.privilege)
        (by simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint]) (.pure ⟨rfl, rfl⟩)) (Result .store))
    rw [config.transform.privilege, SupervisorBare.effective_supervisor rs (.Store .Data) (Or.inr config.transform.mprv)]
    apply prefix_except (value := Privilege.Supervisor) (lift_except (pure_plan _ _ _) (Result .store))
    apply prefix_except (value := SATPMode.Bare) (lift_except mode (Result .store))
    apply prefix_except (value := false) (pure_plan _ _ _)
    apply prefix_except (value := true) (pure_plan _ _ _)
    apply OneWrite.bind (value := fun b => (Except.ok b : Except (Result .store) Bool))
    · apply OneWrite.prefix (lift_except trans (Result .store))
      apply prefix_except (value := ()) (pure_plan _ _ _)
      apply OneWrite.prefix (lift_except hea (Result .store))
      dsimp only [ExceptT.bindCont]
      have sliced : OneWrite (footprint shares) rs address word
          (mem_write_value (.Physaddr address) 4 (BitVec.setWidth 32 (Sail.BitVec.extractLsb word 31 0))
            (.Store .Data) .PBMT_PMA false false false) (fun b => .Ok b) := by
        simpa only [SupervisorWrite4.full_word, BitVec.setWidth_eq] using value
      apply OneWrite.bind (one_lift sliced (Result .store))
      intro b; rfl
    · intro b; rfl
  · intro b; rfl

end Xv6.Kernel.PushOffWord4Bare.Write
