import Xv6.Kernel.Sv39AddressPure

namespace Xv6.Kernel.Sv39Address
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

private theorem bind_returns {fp : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM α} {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns fp rs program value rs)
    (rest : RegisterPlan.Returns fp rs (next value) result rs) :
    RegisterPlan.Returns fp rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem pure_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (value : α) :
    RegisterPlan.Returns fp rs (pure value) value rs := .pure ⟨rfl,rfl⟩

private theorem read_plan (shares : Shares) (rs : RegisterFile) (r : Register) (dq : DFrac)
    (member : (r,dq) ∈ footprint shares) :
    RegisterPlan.Returns (footprint shares) rs (PreSail.readReg r) (rs r) rs :=
  .read member (.pure ⟨rfl,rfl⟩)

private theorem lift_except {fp : RegisterFootprint.Footprint} {program : SailM α}
    {rs : RegisterFile} {value : α} (plan : RegisterPlan.Returns fp rs program value rs) (ε : Type) :
    RegisterPlan.Returns fp rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change RegisterPlan.Returns fp rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact bind_returns plan (pure_plan fp rs _)

private theorem except_bind {fp : RegisterFootprint.Footprint} {program : SailME ε α}
    {next : α → SailME ε β} {rs : RegisterFile} {a : α} {b : Except ε β}
    (first : RegisterPlan.Returns fp rs program.run (.ok a) rs)
    (second : RegisterPlan.Returns fp rs (next a).run b rs) :
    RegisterPlan.Returns fp rs (program >>= next).run b rs := bind_returns first second

private theorem prefix_except {fp rs} {body : SailM α} {segment : SailME ε γ} {value : γ}
    {next : γ → SailME ε β} {tail}
    (before : RegisterPlan.Returns fp rs segment.run (.ok value) rs)
    (after : Boundary fp rs body (next value).run tail) :
    Boundary fp rs body (segment >>= next).run tail := .prefix before after

private theorem boundary_body_eq {fp rs} {body : SailM α} {program : SailM β} {tail : α → SailM β}
    (eq : program = body >>= tail) : Boundary fp rs body program tail := by
  rw [eq]
  exact .body _

private theorem boundary_bind {fp rs} {body : SailM α} {program : SailM β} {tail : α → SailM β}
    (cut : Boundary fp rs body program tail) (next : β → SailM γ) :
    Boundary fp rs body (program >>= next) (fun value => tail value >>= next) := by
  induction cut with
  | body => rw [BootPmp.sail_bind_assoc]; exact .body _
  | «prefix» first rest ih => rw [BootPmp.sail_bind_assoc]; exact .prefix first ih

private theorem boundary_bind_eq {fp rs} {body : SailM α} {program : SailM β} {tail : α → SailM β}
    (cut : Boundary fp rs body program tail) (next : β → SailM γ) (out : α → SailM γ)
    (eq : ∀ value, tail value >>= next = out value) :
    Boundary fp rs body (program >>= next) out := by
  have same : (fun value => tail value >>= next) = out := funext eq
  rw [← same]
  exact boundary_bind cut next

set_option maxRecDepth 100000 in
theorem canonical shares rs tree (config : Config rs (PtTree.base tree)) address access
    (supported : Supported access) (effective : Effective rs access) (canon : Canonical address) :
    Boundary (footprint shares) rs
      (KptTranslate.program 0#16 tree (vpn address) access (mxr rs) (doSum rs))
      (program address access) (resume address access) := by
  have support : SupervisorBare.Supported access := by cases supported <;> constructor
  unfold program translateAddr _root_.Sail.SailME.run PreSail.PreSailME.run
  apply boundary_bind_eq (tail := fun response =>
    (monadLift (resume address access response) : SailME Result Result).run)
  · apply prefix_except (lift_except (read_plan shares rs .mstatus shares.status (by simp [footprint, SupervisorBare.footprint])) _)
    apply prefix_except (lift_except (read_plan shares rs .cur_privilege shares.privilege (by simp [footprint, SupervisorBare.footprint])) _)
    rw [config.privilege, SupervisorBare.effective_supervisor rs access effective]
    apply prefix_except (lift_except (pure_plan (footprint shares) rs Privilege.Supervisor) _)
    apply prefix_except (lift_except (mode shares rs _ config) _)
    rw [SupervisorBare.not_shadow access support]
    apply prefix_except (lift_except (pure_plan (footprint shares) rs false) _)
    apply prefix_except (pure_plan (footprint shares) rs _)
    apply prefix_except (lift_except (satp shares rs) _)
    apply prefix_except (lift_except (pure_plan (footprint shares) rs ()) _)
    have test : (address != sign_extend (m := 64) (_root_.Sail.BitVec.extractLsb address 38 0)) = false := by
      change (address != (address.extractLsb' 0 39).signExtend 64) = false
      exact bne_eq_false_iff_eq.mpr canon
    simp only [bits_of_virtaddr]
    erw [test]
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply prefix_except (lift_except (read_plan shares rs .mstatus shares.status (by simp [footprint, SupervisorBare.footprint])) _)
    apply prefix_except (pure_plan (footprint shares) rs _)
    apply prefix_except (lift_except (read_plan shares rs .mstatus shares.status (by simp [footprint, SupervisorBare.footprint])) _)
    apply prefix_except (pure_plan (footprint shares) rs _)
    have asidEq : zero_extend (m := 16) (satp_to_asid (k_n := 64) (rs .satp)) = 0#16 := config.rooted.2.1
    have ppnEq : (satp_to_ppn (k_n := 64) (rs .satp)).setWidth 44 = PtTree.base tree := config.rooted.2.2
    have vpnEq : (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb address 38 0) 38 12).setWidth 27 = vpn address := by
      change (address.extractLsb' 0 39).extractLsb' 12 27 = address.extractLsb' 12 27
      exact BitVec.extractLsb'_extractLsb'_of_le (by decide)
    erw [asidEq, ppnEq, vpnEq]
    apply boundary_body_eq
    change ((KptTranslate.program 0#16 tree (vpn address) access (mxr rs) (doSum rs) >>=
      fun value => pure (Except.ok value : Except Result KptTranslate.Result)) >>= _) = _
    rw [BootPmp.sail_bind_assoc]
    apply congrArg (fun next : KptTranslate.Result → SailM (Except Result Result) =>
      KptTranslate.program 0#16 tree (vpn address) access (mxr rs) (doSum rs) >>= next)
    funext response
    cases response with
    | Ok pair => rcases pair with ⟨ppn,pbmt,ext⟩; rfl
    | Err pair =>
      rcases pair with ⟨error,ext⟩
      simp only [resume, exception access supported, BootPmp.sail_pure_bind]
      rfl
  · intro response
    cases response with
    | Ok pair => rcases pair with ⟨ppn,pbmt,ext⟩; rfl
    | Err pair =>
      rcases pair with ⟨error,ext⟩
      simp only [resume, exception access supported, BootPmp.sail_pure_bind]
      rfl

set_option maxRecDepth 100000 in
theorem noncanonical shares rs root (config : Config rs root) address access
    (supported : Supported access) (effective : Effective rs access) (canon : ¬ Canonical address) :
    RegisterPlan.Returns (footprint shares) rs (program address access)
      (.Err (pageFault access, ())) rs := by
  have support : SupervisorBare.Supported access := by cases supported <;> constructor
  unfold program translateAddr _root_.Sail.SailME.run PreSail.PreSailME.run
  apply bind_returns (value := Except.ok (.Err (pageFault access, ())))
  · apply except_bind (lift_except (read_plan shares rs .mstatus shares.status (by simp [footprint, SupervisorBare.footprint])) _)
    apply except_bind (lift_except (read_plan shares rs .cur_privilege shares.privilege (by simp [footprint, SupervisorBare.footprint])) _)
    rw [config.privilege, SupervisorBare.effective_supervisor rs access effective]
    apply except_bind (lift_except (pure_plan (footprint shares) rs Privilege.Supervisor) _)
    apply except_bind (lift_except (mode shares rs _ config) _)
    rw [SupervisorBare.not_shadow access support]
    apply except_bind (lift_except (pure_plan (footprint shares) rs false) _)
    apply except_bind (pure_plan (footprint shares) rs _)
    apply except_bind (lift_except (satp shares rs) _)
    apply except_bind (lift_except (pure_plan (footprint shares) rs ()) _)
    have test : (address != sign_extend (m := 64) (_root_.Sail.BitVec.extractLsb address 38 0)) = true := by
      change (address != (address.extractLsb' 0 39).signExtend 64) = true
      exact bne_iff_ne.mpr canon
    simp only [bits_of_virtaddr]
    erw [test]
    simp only [↓reduceIte]
    rw [exception access supported]
    apply except_bind (lift_except (pure_plan (footprint shares) rs _) _)
    exact .pure ⟨rfl,rfl⟩
  · exact .pure ⟨rfl,rfl⟩


end Xv6.Kernel.Sv39Address
