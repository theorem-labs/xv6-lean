import Xv6.Kernel.Sv39HitSpec
import Xv6.Kernel.TlbCoherenceLink
import Xv6.Kernel.KptLeafLink
import MachCSL.Logic.SupervisorPteADPlan

namespace Xv6.Kernel.Sv39Hit
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem raw_factor asid vpn idx ent access mxr doSum :
    program asid vpn idx ent access mxr doSum =
      permission ent access mxr doSum >>= afterPermission vpn idx ent access mxr doSum := by
  have pte : tlb_get_pte 8 ent = ent.pte := BitVec.extractLsb'_eq_self
  unfold program translate_TLB_hit
  change (check_PTE_permission access .Supervisor mxr doSum
      (PteCanonical.flags (tlb_get_pte 8 ent)) (ext_bits_of_PTE (tlb_get_pte 8 ent)) () >>= _) = _
  rw [pte]
  apply congrArg (fun next : PTE_Check → SailM Result => permission ent access mxr doSum >>= next)
  funext checked
  cases checked with
  | PTE_Check_Failure pair => cases pair; rfl
  | PTE_Check_Success ext =>
    cases ext
    unfold afterPermission
    change (update_and_write_pte 39 vpn ent.pteAddr (tlb_get_pte 8 ent)
      (tlb_get_level 39 ent) access .Supervisor mxr doSum () >>= _) = _
    rw [pte]
    apply congrArg (fun next : UpdateResult → SailM Result =>
      update_and_write_pte 39 vpn ent.pteAddr ent.pte (tlb_get_level 39 ent)
        access .Supervisor mxr doSum () >>= next)
    funext updated
    cases updated with
    | Err pair => cases pair; rfl
    | Ok pair => rcases pair with ⟨word, ext⟩; cases word <;> rfl

theorem entry_update asid vpn idx p2 p1 word access mxr doSum :
    afterPermission vpn idx (entry asid vpn p2 p1 word) access mxr doSum (.PTE_Check_Success ()) =
      SupervisorPteAD.program vpn (PtTree.addr0 p1 vpn) word access mxr doSum >>=
        afterUpdate vpn idx (entry asid vpn p2 p1 word) := by
  unfold afterPermission
  rw [TlbCoherence.get_level]
  rfl

theorem kernel_head asid vpn idx p2 p1 ppn perm a d access
    (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows perm access) mxr doSum :
    program asid vpn idx (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d)) access mxr doSum =
      head (KptLeaf.word ppn perm a d) access >>=
        remainder vpn idx (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d))
          (PtTree.addr0 p1 vpn) access mxr doSum := by
  rw [raw_factor]
  have check : permission (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d)) access mxr doSum =
      pure (.PTE_Check_Success ()) := by
    unfold permission
    change check_PTE_permission access .Supervisor mxr doSum
      (PteCanonical.flags (KptLeaf.word ppn perm a d))
      (ext_bits_of_PTE (KptLeaf.word ppn perm a d)) () = _
    rw [KptLeaf.word_flags, KptLeaf.word_ext]
    exact KptLeaf.permission_eq perm a d access supported allowed mxr doSum
  rw [check, BootPmp.sail_pure_bind, entry_update, SupervisorPteAD.program_eq]
  cases needs : update_PTE_Bits (KptLeaf.word ppn perm a d) access with
  | none => simp [head, remainder, entry, TlbCoherence.entry, Sv39Tlb.entry, needs, BootPmp.sail_pure_bind]
  | some word =>
    simp only [head, needs]
    rw [BootPmp.sail_bind_assoc]
    apply congrArg (fun next : Bool → SailM Result => SupervisorPteAD.gate >>= next)
    funext enabled
    simp only [remainder, entry, TlbCoherence.entry, Sv39Tlb.entry, needs]

theorem denied asid vpn idx ent access mxr doSum failure
    (failed : permission ent access mxr doSum = pure (.PTE_Check_Failure ((), failure))) :
    program asid vpn idx ent access mxr doSum = pure (.Err (ext_get_ptw_error failure, ())) := by
  rw [raw_factor, failed, BootPmp.sail_pure_bind]
  rfl

theorem enabled_remainder vpn idx ent address access mxr doSum
    (needs : (update_PTE_Bits ent.pte access).isSome = true) :
    remainder vpn idx ent address access mxr doSum true =
      (read_pte_exclusive (.Physaddr address) 8 >>=
        SupervisorPteAD.afterRead vpn address access mxr doSum) >>= afterUpdate vpn idx ent := by
  unfold remainder
  cases eq : update_PTE_Bits ent.pte access with
  | none => simp [eq] at needs
  | some word => rfl

theorem disabled_remainder vpn idx ent address access mxr doSum
    (needs : (update_PTE_Bits ent.pte access).isSome = true) :
    remainder vpn idx ent address access mxr doSum false =
      pure (.Err (.PTW_PTE_Needs_Update (), ())) := by
  unfold remainder
  cases eq : update_PTE_Bits ent.pte access with
  | none => simp [eq] at needs
  | some word => rfl

theorem write_false word ext : SupervisorPteAD.afterWrite word ext (.Ok false) =
    internal_error "sys/vmem.sail" 226 "PTE conditional write failed" := rfl

theorem write_error word ext error : SupervisorPteAD.afterWrite word ext (.Err error) =
    pure (.Err (.PTW_No_Access (), ext)) := rfl

theorem coherent_resume asid tree rs vpn ent response
    (coherent : TlbCoherence.Coherent asid tree (rs .tlb))
    (resident : (rs .tlb)[TlbCoherence.index vpn]? = some (some ent))
    (variant : UpdateVariant ent response) :
    TlbCoherence.Coherent asid tree
      (updateAfter rs (TlbCoherence.index vpn) ent response .tlb) := by
  cases response with
  | Err error => exact coherent
  | Ok pair =>
    rcases pair with ⟨word, ext⟩
    cases word with
    | none => exact coherent
    | some word => exact TlbCoherence.refresh asid tree (rs .tlb) vpn ent word coherent resident variant

end Xv6.Kernel.Sv39Hit
