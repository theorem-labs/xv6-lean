import Xv6.Kernel.Sv39WalkPure

namespace Xv6.Kernel.Sv39Walk
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- The actual leaf response branches, including faults. -/
def afterLeaf (pte : BitVec 64) (address : physaddr) (level : Nat) (global : Bool) :
    _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → SailM Result
  | .Err error => pure (.Err error)
  | .Ok (ppn, pbmt, ext) => pure (.Ok (⟨ppn, pte, address, level, pbmt, global⟩, ext))

/-- Both the recursive and leaf branches of the generated validity test. -/
def afterInvalid (vpn : BitVec 27) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) (pte : BitVec 64) (address : physaddr) (level : Nat)
    (global invalid : Bool) : SailM Result :=
  let flags := PteCanonical.flags pte
  let global := global || (_get_PTE_Flags_G flags == 1#1)
  if LeanPaperStock.Functions.not invalid && (pte_is_non_leaf flags && level >b 0) then
    pt_walk 39 vpn access .Supervisor mxr doSum (PPN_of_PTE (k_pte_size := 64) pte) (level - 1) global ()
  else check_leaf_pte 39 vpn access .Supervisor mxr doSum pte address level () >>=
    afterLeaf pte address level global

/-- The ordinary PTE read retains its complete error continuation. -/
def afterRead (vpn : BitVec 27) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) (address : physaddr) (level : Nat) (global : Bool) :
    SupervisorPteRead.Result → SailM Result
  | .Err _ => pure (.Err (.PTW_No_Access (), ()))
  | .Ok pte => pte_is_invalid (PteCanonical.flags pte) (ext_bits_of_PTE pte) >>=
      afterInvalid vpn access mxr doSum pte address level global

theorem node_eq (vpn : BitVec 27) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) (ppn : BitVec 44) (level : Fin 3) (global : Bool) :
    pt_walk 39 vpn access .Supervisor mxr doSum ppn level.val global () =
      read_pte (.Physaddr (addressAt ppn (index vpn level.val))) 8 >>=
        afterRead vpn access mxr doSum (.Physaddr (addressAt ppn (index vpn level.val))) level.val global := by
  rcases level with ⟨level, lt⟩
  have cases : level = 0 ∨ level = 1 ∨ level = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> rw [pt_walk.eq_def]
  all_goals
    change (read_pte _ 8 >>= _) = _
    apply congrArg (fun next : SupervisorPteRead.Result → SailM Result => read_pte _ 8 >>= next)
    funext response
    cases response with
    | Err error => rfl
    | Ok pte =>
      change (pte_is_invalid _ _ >>= _) = (pte_is_invalid _ _ >>= _)
      congr 1
      funext invalid
      unfold afterInvalid
      split <;> rename_i condition
      · simp only [PteCanonical.flags] at *
        erw [if_pos condition]
        rfl
      · simp only [PteCanonical.flags] at *
        erw [if_neg condition]
        apply congrArg (fun next : _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → SailM Result =>
          check_leaf_pte 39 vpn access .Supervisor mxr doSum _ _ _ () >>= next)
        funext checked
        cases checked with
        | Err error => cases error; rfl
        | Ok value => rcases value with ⟨ppn, pbmt, ext⟩; rfl

theorem pointer_next (vpn : BitVec 27) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) (ppn : BitVec 44) (address : physaddr)
    (level : Nat) (positive : 0 < level) (global : Bool) :
    afterInvalid vpn access mxr doSum (pointer ppn) address level global false =
      pt_walk 39 vpn access .Supervisor mxr doSum ppn (level - 1) global () := by
  unfold afterInvalid
  rw [pointer_flags]
  have nonleaf : pte_is_non_leaf 1#8 = true := rfl
  have glob : (_get_PTE_Flags_G 1#8 == 1#1) = false := rfl
  have pos : (level >b 0) = true := by exact decide_eq_true positive
  simp only [LeanPaperStock.Functions.not, Bool.not_false, nonleaf, glob, pos,
    Bool.true_and, Bool.or_false, ↓reduceIte]
  erw [pointer_ppn]

theorem leaf_next (vpn : BitVec 27) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) (ppn : BitVec 44) (permission : KptLeaf.Permission)
    (a d : Bool) (address : physaddr) (global : Bool) :
    afterInvalid vpn access mxr doSum (KptLeaf.word ppn permission a d) address 0 global false =
      KptLeaf.program ppn permission a d vpn address access mxr doSum >>=
        afterLeaf (KptLeaf.word ppn permission a d) address 0 global := by
  unfold afterInvalid
  erw [KptLeaf.word_flags]
  have glob : (_get_PTE_Flags_G (KptLeaf.flagByte permission a d) == 1#1) = false := by
    cases permission <;> cases a <;> cases d <;> rfl
  simp only [glob, Bool.or_false, show (0 >b 0) = false from rfl, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Level zero executes its first validity check and then the actual leaf
validator, including the validator's repeated validity check. -/
theorem leaf_plan (rs : RegisterFile) (path : Path) (vpn : BitVec 27)
    (permission : KptLeaf.Permission) (a d : Bool) (access : MemoryAccessType mem_payload)
    (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    (mxr doSum global : Bool) :
    RegisterPlan.Returns [] rs
      (afterRead vpn access mxr doSum (.Physaddr (address path vpn 0)) 0 global
        (.Ok (KptLeaf.word path.leaf permission a d)))
      (.Ok (output path vpn permission global a d, ())) rs := by
  unfold afterRead
  apply RegisterPlan.Plan.bind (P := fun value after =>
    value = false ∧ after = rs)
  · erw [KptLeaf.word_flags, KptLeaf.word_ext]
    exact KptLeaf.valid_plan rs permission a d
  · intro value after same
    rcases same with ⟨returned, unchanged⟩
    subst after
    subst value
    rw [leaf_next]
    apply RegisterPlan.Plan.bind (KptLeaf.check_plan rs path.leaf permission a d vpn
      (.Physaddr (address path vpn 0)) access supported allowed mxr doSum)
    intro value after same
    rcases same with ⟨rfl, rfl⟩
    exact .pure ⟨rfl, rfl⟩

end Xv6.Kernel.Sv39Walk
