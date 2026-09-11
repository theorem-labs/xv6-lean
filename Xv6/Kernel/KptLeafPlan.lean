import Xv6.Kernel.KptLeafWordProofs
import MachCSL.Logic.RegisterPlanProofs

namespace Xv6.Kernel.KptLeaf
open MachCSL.Machine LeanPaperStock.Functions
open MachCSL.Logic
open _root_.Sail.ConcurrencyInterfaceV1.Free

theorem permission_eq (permission : Permission) (a d : Bool)
    (access : MemoryAccessType mem_payload) (supported : Supported access)
    (allowed : Allows permission access) (mxr doSum : Bool) :
    check_PTE_permission access .Supervisor mxr doSum (flagByte permission a d) 0#10 () =
      pure (.PTE_Check_Success ()) := by
  cases supported with
  | fetch =>
    change permission = .rx at allowed
    subst permission
    cases a <;> cases d <;> cases mxr <;> cases doSum <;> rfl
  | load =>
    cases permission <;> cases a <;> cases d <;> cases mxr <;> cases doSum <;> rfl
  | store =>
    change permission = .rw at allowed
    subst permission
    cases a <;> cases d <;> cases mxr <;> cases doSum <;> rfl
  | swap aq rl =>
    change permission = .rw at allowed
    subst permission
    cases a <;> cases d <;> cases mxr <;> cases doSum <;> rfl

set_option maxRecDepth 4096 in
theorem valid_plan (rs : RegisterFile) (permission : Permission) (a d : Bool) :
    RegisterPlan.Returns [] rs (pte_is_invalid (flagByte permission a d) 0#10) false rs := by
  cases permission <;> cases a <;> cases d <;>
    unfold pte_is_invalid <;>
    simp only [currentlyEnabled] <;>
    apply RegisterPlan.Plan.readAny <;> intro env1 <;>
    apply RegisterPlan.Plan.readAny <;> intro isa1 <;>
    apply RegisterPlan.Plan.readAny <;> intro isa2 <;>
    apply RegisterPlan.Plan.readAny <;> intro env2 <;>
    apply RegisterPlan.Plan.readAny <;> intro isa3 <;>
    exact .pure ⟨rfl, rfl⟩

private theorem returns_bind {rs : RegisterFile} {program : SailM α}
    {next : α → SailM β} {value : α} {result : β}
    (first : RegisterPlan.Returns [] rs program value rs)
    (rest : RegisterPlan.Returns [] rs (next value) result rs) :
    RegisterPlan.Returns [] rs (program >>= next) result rs :=
  RegisterPlan.Plan.bind first fun _ _ ⟨rfl, rfl⟩ => rest

private theorem lift_except {program : SailM α} {rs : RegisterFile} {value : α}
    (plan : RegisterPlan.Returns [] rs program value rs) (ε : Type) :
    RegisterPlan.Returns [] rs (monadLift program : SailME ε α).run (.ok value) rs := by
  change RegisterPlan.Returns [] rs (program >>= fun a => pure (Except.ok a)) (.ok value) rs
  exact returns_bind plan (.pure ⟨rfl, rfl⟩)

private theorem except_bind {program : SailME ε α} {next : α → SailME ε β}
    {rs : RegisterFile} {a : α} {b : Except ε β}
    (first : RegisterPlan.Returns [] rs program.run (.ok a) rs)
    (second : RegisterPlan.Returns [] rs (next a).run b rs) :
    RegisterPlan.Returns [] rs (program >>= next).run b rs := returns_bind first second

set_option maxRecDepth 4096 in
theorem check_plan (rs : RegisterFile) (ppn : BitVec 44) (permission : Permission)
    (a d : Bool) (vpn : BitVec 27) (address : physaddr)
    (access : MemoryAccessType mem_payload) (supported : Supported access)
    (allowed : Allows permission access) (mxr doSum : Bool) :
    RegisterPlan.Returns [] rs (program ppn permission a d vpn address access mxr doSum)
      (.Ok (ppn, .PBMT_PMA, ())) rs := by
  unfold program check_leaf_pte
  dsimp only
  erw [show Mk_PTE_Flags (_root_.Sail.BitVec.extractLsb (word ppn permission a d) 7 0) =
    flagByte permission a d from word_flags ppn permission a d, word_ext]
  unfold _root_.Sail.SailME.run PreSail.PreSailME.run
  apply returns_bind (value := Except.ok (.Ok (ppn, .PBMT_PMA, ())))
  · apply except_bind (lift_except (valid_plan rs permission a d) _)
    simp only [Bool.false_eq_true, ↓reduceIte, flag_nonleaf]
    erw [word_ppn]
    simp only [show (0 >b 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [permission_eq permission a d access supported allowed mxr doSum]
    simp only [currentlyEnabled]
    apply RegisterPlan.Plan.readAny
    intro isa
    dsimp only [_root_.Sail.ArchSem.FreeM.bind, ExceptT.bindCont]
    simp only [show (_get_PTE_Ext_N 0#10 == 1#1) = false from rfl, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]
    apply RegisterPlan.Plan.readAny
    intro environment
    dsimp only [Function.comp_def, _root_.Sail.ArchSem.FreeM.bind, ExceptT.bindCont]
    split <;> exact .pure ⟨rfl, rfl⟩
  · exact .pure ⟨rfl, rfl⟩

theorem planSpec : PlanSpec := ⟨permission_eq, valid_plan, check_plan⟩

end Xv6.Kernel.KptLeaf
