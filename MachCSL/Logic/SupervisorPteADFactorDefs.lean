import MachCSL.Logic.SupervisorPteADDefs

namespace MachCSL.Logic.SupervisorPteAD
open MachCSL.Machine LeanPaperStock.Functions

/-- Every actual write response is retained, including the real internal
error on a false Boolean response. -/
def afterWrite (word : BitVec 64) (ext : Unit) : SupervisorPteWrite.Result → SailM Result
  | .Ok true => pure (.Ok (some word, ext))
  | .Ok false => internal_error "sys/vmem.sail" 226 "PTE conditional write failed"
  | .Err _ => pure (.Err (.PTW_No_Access (), ext))

def afterCheck (address physical : BitVec 64) (access : MemoryAccessType mem_payload) :
    _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → SailM Result
  | .Err (error, ext) => pure (.Err (error, ext))
  | .Ok (_, _, ext) => do
    match update_PTE_Bits physical access with
    | none => pure (.Ok (some physical, ext))
    | some word => write_pte_conditional (.Physaddr address) 8 word >>= afterWrite word ext

def afterRead (vpn : BitVec 27) (address : BitVec 64) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) : SupervisorPteRead.Result → SailM Result
  | .Err _ => pure (.Err (.PTW_No_Access (), ()))
  | .Ok physical =>
    check_leaf_pte 39 vpn access .Supervisor mxr doSum physical (.Physaddr address) 0 () >>=
      afterCheck address physical access

def afterGate (vpn : BitVec 27) (address : BitVec 64) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) (adue : Bool) : SailM Result :=
  if adue then read_pte_exclusive (.Physaddr address) 8 >>= afterRead vpn address access mxr doSum
  else pure (.Err (.PTW_PTE_Needs_Update (), ()))

end MachCSL.Logic.SupervisorPteAD
