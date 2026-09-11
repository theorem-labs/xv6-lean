import Xv6.Kernel.TlbCoherenceDefs
import Xv6.Kernel.KptLeafDefs
import MachCSL.Logic.SupervisorPteADFactorDefs
import MachCSL.Logic.RegisterWPDefs

/-! Actual supervisor hit factorization, with its unresolved atomic A/D
remainder retained as a Sail program. No successful memory result is assumed. -/
namespace Xv6.Kernel.Sv39Hit
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Result := _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)
abbrev UpdateResult := SupervisorPteAD.Result
abbrev entry := TlbCoherence.entry

def program (asid : BitVec 16) (vpn : BitVec 27) (idx : Nat) (ent : TLB_Entry)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool) : SailM Result :=
  translate_TLB_hit 39 asid vpn access .Supervisor mxr doSum () idx ent

def permission (ent : TLB_Entry) (access : MemoryAccessType mem_payload)
    (mxr doSum : Bool) : SailM PTE_Check :=
  check_PTE_permission access .Supervisor mxr doSum (PteCanonical.flags ent.pte)
    (ext_bits_of_PTE ent.pte) ()

/-- Both returned PPN and PBMT come from the original cached entry, even
when a successful update supplies a different word. -/
def afterUpdate (vpn : BitVec 27) (idx : Nat) (ent : TLB_Entry) : UpdateResult → SailM Result
  | .Err error => pure (.Err error)
  | .Ok (none, ext) => do
      pure (.Ok (tlb_get_ppn 39 ent vpn, ← tlb_get_pbmt ent, ext))
  | .Ok (some word, ext) => do
      write_TLB idx (tlb_set_pte (k_n := 8) ent word)
      pure (.Ok (tlb_get_ppn 39 ent vpn, ← tlb_get_pbmt ent, ext))

def afterPermission (vpn : BitVec 27) (idx : Nat) (ent : TLB_Entry)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool) : PTE_Check → SailM Result
  | .PTE_Check_Failure (ext, failure) => pure (.Err (ext_get_ptw_error failure, ext))
  | .PTE_Check_Success ext =>
      update_and_write_pte 39 vpn ent.pteAddr ent.pte (tlb_get_level 39 ent)
        access .Supervisor mxr doSum ext >>= afterUpdate vpn idx ent

/-- The cached path does not read MENVCFG. The other path retains its
actual gate, with no assumption that ADUE is enabled. -/
def head (cached : BitVec 64) (access : MemoryAccessType mem_payload) : SailM Bool :=
  match update_PTE_Bits cached access with
  | none => pure false
  | some _ => SupervisorPteAD.gate

def headValue (rs : RegisterFile) (cached : BitVec 64)
    (access : MemoryAccessType mem_payload) : Bool :=
  (update_PTE_Bits cached access).isSome && SupervisorPteAD.enabled rs

/-- The enabled arm is the real exclusive-read/check/conditional-write
program. Its errors and false conditional-write terminal event remain intact. -/
def remainder (vpn : BitVec 27) (idx : Nat) (ent : TLB_Entry) (address : BitVec 64)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool) (enabled : Bool) : SailM Result :=
  match update_PTE_Bits ent.pte access with
  | none => afterUpdate vpn idx ent (.Ok (none, ()))
  | some _ => SupervisorPteAD.afterGate vpn address access mxr doSum enabled >>=
      afterUpdate vpn idx ent

def updateValue (vpn : BitVec 27) (ent : TLB_Entry) : UpdateResult → Result
  | .Err error => .Err error
  | .Ok (_, ext) => .Ok (tlb_get_ppn 39 ent vpn, .PBMT_PMA, ext)

def updateAfter (rs : RegisterFile) (idx : Nat) (ent : TLB_Entry) : UpdateResult → RegisterFile
  | .Ok (some word, _) => TlbCoherence.refreshAfter rs idx ent word
  | _ => rs

/-- Only a successful Some response needs a canonical relation to preserve
coherence. This is not a promise that the memory remainder returns Some. -/
def UpdateVariant (ent : TLB_Entry) : UpdateResult → Prop
  | .Ok (some word, _) => TlbCoherence.Variant ent.pte word
  | _ => True

def footprint (environment : DFrac) : RegisterFootprint.Footprint :=
  [(.menvcfg, environment), (.tlb, .own 1)]

def cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (environment : DFrac) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint environment)

end Xv6.Kernel.Sv39Hit
