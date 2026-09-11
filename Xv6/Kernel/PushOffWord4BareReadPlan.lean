import Xv6.Kernel.PushOffWord4BarePure

namespace Xv6.Kernel.PushOffWord4Bare.Read
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions SupervisorFetchRead
open _root_.Sail.ConcurrencyInterfaceV1.Free

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
    {req : MemoryReadWP.ReadRequest 4} {program : SailM α} {tail}
    (cut : Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen_plan first members) ih

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {address : BitVec 64} {program : SailM α} {value}
    (cut : OneRead small rs address 4 program value)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : OneRead large rs address 4 program value := by
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

private theorem prefix_except {fp rs address} {segment : SailME ε β} {value : β}
    {next : β → SailME ε α} {result}
    (before : RegisterPlan.Returns fp rs segment.run (.ok value) rs)
    (after : OneRead fp rs address 4 (next value).run result) :
    OneRead fp rs address 4 (segment >>= next).run result := OneRead.prefix before after

private theorem one_lift {fp rs address} {program : SailM α} {value}
    (before : OneRead fp rs address 4 program value) (ε : Type) :
    OneRead fp rs address 4 (monadLift program : SailME ε α).run (fun word => Except.ok (value word)) := by
  exact OneRead.bind before _ _ (fun _ => rfl)

theorem effective_plan (shares : Shares) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Supervisor) (clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1) :
    RegisterPlan.Returns (footprint shares) rs
      (SupervisorMemOuter.effective (.Load .Data)) .Supervisor rs := by
  apply widen_plan (SupervisorMemOuter.effective_plan (SupervisorBareFetch.outerShares shares.bare) rs _ priv (Or.inr clear))
  intro cell member
  simp only [SupervisorMemOuter.footprint, SupervisorBareFetch.outerShares, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint]

theorem outer_boundary (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (config : Config rs) (range : SupervisorPhysical.RamRange address 4)
    (aligned : is_aligned_paddr (.Physaddr address) 4 = true) :
    OneRead (footprint shares) rs address 4
      (mem_read (.Load .Data) .PBMT_PMA (.Physaddr address) 4 false false false)
      (fun word => .Ok word) := by
  change OneRead _ _ _ _ (SupervisorMemOuter4.readProgram address) _
  rw [SupervisorMemOuter4.read_factor]
  apply OneRead.prefix (effective_plan shares rs config.transform.privilege config.transform.mprv)
  rw [SupervisorMemOuter4.read_supervisor]
  apply OneRead.bind (value := fun word => .Ok (word, ()))
  · apply widen (SupervisorRead4.checked_boundary shares.bare.physical rs address config.tor range config.htif KptHardware.ramRegion (pma rs config address range) (by rfl) aligned)
    intro cell member
    exact List.mem_append_right _ (List.mem_append_right _ member)
  · intro word; rfl

theorem translate_boundary (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (config : Config rs) (range : SupervisorPhysical.RamRange address 4)
    (aligned : is_aligned_paddr (.Physaddr address) 4 = true) :
    OneRead (footprint shares) rs address 4
      (translate_and_read_value (.Virtaddr address) 4 (.Load .Data) false false false)
      (fun word => .Ok (.Physaddr address, word)) := by
  have trans : RegisterPlan.Returns (footprint shares) rs
      (translateAddr (.Virtaddr address) (.Load .Data))
      (.Ok (.Physaddr address, .PBMT_PMA, ())) rs := by
    apply widen_plan (SupervisorBare.mprv_zero_plan shares.bare.translation rs (bare_config rs config) address _ .load config.transform.mprv)
    intro cell member
    exact List.mem_append_right _ (List.mem_append_left _ member)
  unfold translate_and_read_value
  apply OneRead.prefix trans
  apply OneRead.bind (outer_boundary shares rs address config range aligned)
  intro word; rfl

theorem mode_plan (shares : Shares) (rs : RegisterFile) (config : SupervisorBare.Config rs) :
    RegisterPlan.Returns (footprint shares) rs (translationMode .Supervisor) .Bare rs := by
  apply SupervisorBare.mode_plan rs shares.bare.translation.status shares.bare.translation.satp
    (by simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint])
    (by simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint]) config.sxl config.mode

set_option maxRecDepth 100000 in
theorem program_boundary [Platform] (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (config : Config rs) (range : SupervisorPhysical.RamRange address 4)
    (aligned : KernelDatumWord4.Aligned address) :
    OneRead (footprint shares) rs address 4 (addressProgram .load address 0#32) (fun word => .Ok word) := by
  have ha : is_aligned_vaddr (.Virtaddr address) 4 = true := KptMemory4.alignment address aligned
  have page := KptMemory4.split_page_four address aligned
  have mode := mode_plan shares rs (bare_config rs config)
  have effective := effective_plan shares rs config.transform.privilege config.transform.mprv
  have read := translate_boundary shares rs address config range (KptMemory4.alignment address aligned)
  unfold addressProgram KptMemory4.addressProgram vmem_read_addr _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [ha, LeanPaperStock.Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bits_of_virtaddr, page]
  apply OneRead.bind (value := fun word => (Except.ok (.Ok word) : Except (Result .load) (Result .load)))
  · apply prefix_except (value := ((4, 0) : Int × Int)) (pure_plan (footprint shares) rs _)
    apply prefix_except (value := Privilege.Supervisor) (lift_except effective _)
    apply prefix_except (value := SATPMode.Bare) (lift_except mode _)
    apply prefix_except (value := false) (pure_plan (footprint shares) rs _)
    apply prefix_except (value := (0#32)) (pure_plan (footprint shares) rs _)
    apply OneRead.bind (value := fun word => (Except.ok word : Except (Result .load) (BitVec 32)))
    · apply OneRead.bind (one_lift read (Result .load))
      intro word
      change (pure (Except.ok (Sail.BitVec.updateSubrange (0#32) 31 0 word)) : SailM (Except (Result .load) (BitVec 32))) = _
      rw [SupervisorFetchRead.full_word, BitVec.setWidth_eq]
    · intro word; rfl
  · intro word; rfl

end Xv6.Kernel.PushOffWord4Bare.Read
