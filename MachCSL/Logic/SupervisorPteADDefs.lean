import MachCSL.Logic.SupervisorPteReadDefs
import MachCSL.Logic.SupervisorPteWriteDefs
import Xv6.Kernel.KptLeafDefs

/-! Direct physical kernel-leaf A/D update composition. Shared KPT accessors
are deliberately separate from the concrete slot ownership used here. -/
namespace MachCSL.Logic.SupervisorPteAD
open Iris Iris.BI MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions
open Xv6.Kernel

structure Shares where
  memory : SupervisorPteRead.Shares
  environment : DFrac

def writeShares (shares : Shares) : SupervisorPteWrite.Shares :=
  ⟨shares.memory.pma, shares.memory.cfg, shares.memory.addr, shares.memory.htif⟩

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  SupervisorPteRead.footprint shares.memory ++ [(.menvcfg, shares.environment)]

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

structure Config (rs : RegisterFile) (address : BitVec 64) (region : PMA_Region) : Prop where
  read : SupervisorPteRead.Config rs address region
  write : SupervisorPteWrite.Config rs address region

abbrev Result := _root_.Sail.Result (Option (BitVec 64) × Unit) (PTW_Error × Unit)

def enabled (rs : RegisterFile) : Bool := _get_MEnvcfg_ADUE (rs .menvcfg) == 1#1

/-- Exact gate expression, including repeated pure feature calls and the one
real environment-register read. Its simplification is a later proof. -/
def gate : SailM Bool := do
  pure (((← currentlyEnabled .Ext_Svadu) &&
    ((_get_MEnvcfg_ADUE (← _root_.Sail.readReg .menvcfg)) == 1#1)) ||
    ((LeanPaperStock.Functions.not (← currentlyEnabled .Ext_Svadu)) && (LeanPaperStock.Functions.not (← currentlyEnabled .Ext_Svade))))

def program (vpn : BitVec 27) (address cached : BitVec 64)
    (access : MemoryAccessType mem_payload) (mxr doSum : Bool) : SailM Result :=
  update_and_write_pte 39 vpn (.Physaddr address) cached 0 access .Supervisor mxr doSum ()

inductive Branch where
  | cached
  | disabled
  | reread
  | written (word : BitVec 64)
  deriving DecidableEq

/-- Branch facts are actual pure generated update equations and the actual
ADUE bit. They are supplied by the implementation, not assumed by the WP. -/
def BranchFacts (cached physical : BitVec 64) (access : MemoryAccessType mem_payload)
    (adue : Bool) : Branch → Prop
  | .cached => update_PTE_Bits cached access = none
  | .disabled => (update_PTE_Bits cached access).isSome = true ∧ adue = false
  | .reread => (update_PTE_Bits cached access).isSome = true ∧ adue = true ∧
      update_PTE_Bits physical access = none
  | .written word => (update_PTE_Bits cached access).isSome = true ∧ adue = true ∧
      update_PTE_Bits physical access = some word

def result (physical : BitVec 64) : Branch → Result
  | .cached => .Ok (none, ())
  | .disabled => .Err (.PTW_PTE_Needs_Update (), ())
  | .reread => .Ok (some physical, ())
  | .written word => .Ok (some word, ())

def afterWord (physical : BitVec 64) : Branch → BitVec 64
  | .written word => word
  | _ => physical

def afterReservation (address physical : BitVec 64) (rr : Option Reservation) : Branch → Option Reservation
  | .cached | .disabled => rr
  | .reread => some (snapshot address 8 physical)
  | .written _ => none

/-- Only guards furnished by memory primitives are demanded of the final
continuation. The actual register subevents are still folded separately. -/
def guarded {GF : BundledGFunctors} (branch : Branch) (P : IProp GF) : IProp GF :=
  match branch with
  | .cached | .disabled => P
  | .reread => iprop(▷ P)
  | .written _ => iprop(▷ ▷ P)

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

def receipt (era : Era.Record) (cpu : CPU) (address : BitVec 64) : Branch → IProp GF
  | .cached | .disabled => iprop(emp)
  | .reread => iprop(∃ view : Nat,
      Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view)
  | .written word => iprop(∃ time : Nat, ⌜0 < time⌝ ∗
      Tso.History.logElem capacity.era.history era.logEntries (time - 1)
        ⟨snapshot address 8 word, hartAgent cpu⟩ ∗
      Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) time)

def clientResources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (address physical reference : BitVec 64) (bound : Nat) (rr : Option Reservation)
    (branch : Branch) : IProp GF :=
  iprop(cells capacity era cpu rs shares ∗
    TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte (afterWord physical branch))
      bound (PteCanonical.slotSet reference) ∗
    Reservations.resvFrag capacity.era.reservations era.reservations cpu
      (afterReservation address physical rr branch) ∗
    receipt capacity era cpu address branch ∗
    ⌜PteCanonical.canon (afterWord physical branch) = reference⌝)

def finish [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (address cached physical reference : BitVec 64) (bound : Nat) (rr : Option Reservation)
    (access : MemoryAccessType mem_payload) (continuation : Result → SailM Unit)
    (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ branch : Branch, ⌜BranchFacts cached physical access (enabled rs) branch⌝ -∗
    guarded branch iprop(clientResources capacity era cpu rs shares address physical reference bound rr branch -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (continuation (result physical branch))) post))

end MachCSL.Logic.SupervisorPteAD
