import MachCSL.Logic.SupervisorBareFetchDefs
import MachCSL.Logic.SupervisorFetchReadPlan
import MachCSL.Logic.SupervisorMemOuterPlan
import MachCSL.Machine.SupervisorBarePlan

namespace MachCSL.Logic.SupervisorBareFetch
open Iris MachCSL.Machine LeanPaperStock.Functions SupervisorFetchRead
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
    {n : Nat} {req : MemoryReadWP.ReadRequest n} {program : SailM α} {tail}
    (cut : Boundary small rs req program tail)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : Boundary large rs req program tail := by
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen_plan first members) ih

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {address : BitVec 64} {n : Nat} {program : SailM α} {value}
    (cut : OneRead small rs address n program value)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : OneRead large rs address n program value := by
  obtain ⟨tail, cut, success, error⟩ := cut
  exact ⟨tail, widen_boundary cut members, success, error⟩

private theorem outer_plan (shares : Shares) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Supervisor) :
    RegisterPlan.Returns (footprint shares) rs
      (SupervisorMemOuter.effective (.InstructionFetch ())) .Supervisor rs := by
  apply widen_plan (SupervisorMemOuter.effective_plan (outerShares shares) rs _ priv (Or.inl rfl))
  intro cell member
  simp only [SupervisorMemOuter.footprint, outerShares, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [footprint, SupervisorBare.footprint]

theorem read_factor (address : BitVec 64) (n : Nat) :
    mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr address) n false false false =
      (SupervisorMemOuter.effective (.InstructionFetch ()) >>= fun priv =>
        mem_read_priv (.InstructionFetch ()) .PBMT_PMA priv (.Physaddr address) n false false false) := rfl

theorem read_supervisor (address : BitVec 64) (n : Nat) :
    mem_read_priv (.InstructionFetch ()) .PBMT_PMA .Supervisor (.Physaddr address) n false false false =
      (SupervisorFetchRead.program address n >>= fun result => pure (MemoryOpResult_drop_meta result)) := by
  unfold mem_read_priv
  rw [SupervisorMemOuter.read_meta_eq]
  rfl

theorem outer_boundary (shares : Shares) (rs : RegisterFile) (priv : rs .cur_privilege = .Supervisor)
    (address : BitVec 64) (n : Nat) (width : Supported n) (config : SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address n) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    OneRead (footprint shares) rs address n
      (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr address) n false false false)
      (fun word => .Ok word) := by
  rw [read_factor]
  apply OneRead.prefix (outer_plan shares rs priv)
  rw [read_supervisor]
  apply OneRead.bind (value := fun word => .Ok (word, ()))
  · apply widen (checked_boundary shares.physical rs address n width config range disabled region matched grant aligned)
    intro cell member
    exact List.mem_append_right _ member
  · intro word; rfl

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

private theorem prefix_except {fp rs address n} {segment : SailME ε β} {value : β}
    {next : β → SailME ε α} {result}
    (before : RegisterPlan.Returns fp rs segment.run (.ok value) rs)
    (after : OneRead fp rs address n (next value).run result) :
    OneRead fp rs address n (segment >>= next).run result := OneRead.prefix before after

private theorem one_lift {fp rs address n} {program : SailM α} {value}
    (before : OneRead fp rs address n program value) (ε : Type) :
    OneRead fp rs address n (monadLift program : SailME ε α).run (fun word => Except.ok (value word)) := by
  exact OneRead.bind before _ _ (fun _ => rfl)

set_option maxRecDepth 100000 in
theorem fetch_boundary (shares : Shares) (rs : RegisterFile) (bare : SupervisorBare.Config rs)
    (start address : BitVec 64) (n : Nat) (width : Supported n) (config : SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address n) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) :
    OneRead (footprint shares) rs address n (program start address n)
      (fun word => .FetchBytes_Success word) := by
  have trans : RegisterPlan.Returns (footprint shares) rs
      (translateAddr (.Virtaddr address) (.InstructionFetch ()))
      (.Ok (.Physaddr address, .PBMT_PMA, ())) rs := by
    apply widen_plan (SupervisorBare.fetch_plan shares.translation rs bare address)
    intro cell member
    exact List.mem_append_left _ member
  have read := outer_boundary shares rs bare.privilege address n width config range disabled region matched grant aligned
  unfold program fetch_bytes _root_.Sail.SailME.run PreSail.PreSailME.run
  simp only [ext_fetch_check_pc]
  apply OneRead.bind (value := fun word => (Except.ok (.FetchBytes_Success word) : Except (FetchBytes_Result n) (FetchBytes_Result n)))
  · apply prefix_except (value := (.Physaddr address, .PBMT_PMA))
    · apply returns_bind (lift_except trans _)
      exact pure_plan (footprint shares) rs _
    apply OneRead.bind (one_lift read (FetchBytes_Result n))
    intro word
    rfl
  · intro word; rfl

end MachCSL.Logic.SupervisorBareFetch
