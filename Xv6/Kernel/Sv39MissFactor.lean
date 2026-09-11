import Xv6.Kernel.Sv39MissSpec
import MachCSL.Logic.EventPlanCombinators

namespace Xv6.Kernel.Sv39Miss
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem program_eq (asid : BitVec 16) (path : Sv39Walk.Path) (vpn : BitVec 27)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool) :
    program asid path vpn access mxr doSum =
      Sv39Walk.program path vpn access mxr doSum false >>= afterWalk asid vpn access mxr doSum := by
  unfold program translate_TLB_miss Sv39Walk.program
  apply congrArg (fun next : Sv39Walk.Result → SailM Result =>
    pt_walk 39 vpn access .Supervisor mxr doSum path.root 2 false () >>= next)
  funext walked
  cases walked with
  | Err error => cases error; rfl
  | Ok value =>
    rcases value with ⟨walk, ext⟩
    cases walk
    cases ext
    unfold afterWalk
    apply congrArg (fun next : SupervisorPteAD.Result → SailM Result =>
      update_and_write_pte 39 vpn _ _ _ access .Supervisor mxr doSum () >>= next)
    funext updated
    cases updated with
    | Err error => cases error; rfl
    | Ok value =>
      rcases value with ⟨word, ext⟩
      cases word <;> rfl

theorem after_walk (asid : BitVec 16) (path : Sv39Walk.Path) (vpn : BitVec 27)
    (permission : KptLeaf.Permission) (a d : Bool) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) :
    afterWalk asid vpn access mxr doSum (.Ok (Sv39Walk.output path vpn permission false a d, ())) =
      SupervisorPteAD.program vpn (Sv39Walk.address path vpn 0)
        (KptLeaf.word path.leaf permission a d) access mxr doSum >>=
          afterUpdate asid vpn (Sv39Walk.output path vpn permission false a d) := rfl

theorem after_update (asid : BitVec 16) (path : Sv39Walk.Path) (vpn : BitVec 27)
    (permission : KptLeaf.Permission) (a d : Bool) (physical : BitVec 64) (branch : Branch) :
    afterUpdate asid vpn (Sv39Walk.output path vpn permission false a d)
      (SupervisorPteAD.result physical branch) =
      (match branch with
      | .disabled => pure (result path.leaf branch)
      | _ => do
          add_to_TLB 39 asid vpn path.leaf
            (fillWord (KptLeaf.word path.leaf permission a d) physical branch)
            (.Physaddr (Sv39Walk.address path vpn 0)) 0 false
          pure (result path.leaf branch)) := by
  cases branch <;> rfl

end Xv6.Kernel.Sv39Miss
