import MachCSL.Machine.PteCanonicalDefs
import MachCSL.Logic.RegisterPlanDefs
import LeanPaperStock.Vmem

/-! Kernel leaf words and the actual four source-supported access classes. -/
namespace Xv6.Kernel.KptLeaf
open MachCSL.Machine LeanPaperStock.Functions

inductive Permission where
  | rx
  | rw
  deriving DecidableEq

def base : Permission → Nat
  | .rx => 0x0b
  | .rw => 0x07

def flagByte (permission : Permission) (a d : Bool) : BitVec 8 :=
  BitVec.ofNat 8 (base permission + (if a then 64 else 0) + (if d then 128 else 0))

/-- Source mk_pte: zero-extended concatenation of the 44-bit PPN and ten flags. -/
def word (ppn : BitVec 44) (permission : Permission) (a d : Bool) : BitVec 64 :=
  (BitVec.append ppn ((flagByte permission a d).zeroExtend 10)).zeroExtend 64

inductive Supported : MemoryAccessType mem_payload → Prop where
  | fetch : Supported (.InstructionFetch ())
  | load : Supported (.Load .Data)
  | store : Supported (.Store .Data)
  | swap (aq rl : Bool) : Supported (.Atomic (.AMOSWAP, aq, rl, .Data, .Data))

def Allows (permission : Permission) (access : MemoryAccessType mem_payload) : Prop :=
  match access with
  | .InstructionFetch _ => permission = .rx
  | .Load _ => True
  | _ => permission = .rw

def program (ppn : BitVec 44) (permission : Permission) (a d : Bool)
    (vpn : BitVec 27) (address : physaddr) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) :=
  check_leaf_pte 39 vpn access .Supervisor mxr doSum (word ppn permission a d) address 0 ()

end Xv6.Kernel.KptLeaf
