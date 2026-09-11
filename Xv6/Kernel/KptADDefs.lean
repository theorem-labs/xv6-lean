import Xv6.Kernel.KptExclusiveEventDefs
import Xv6.Kernel.KptWriteEventDefs
import MachCSL.Logic.SupervisorPteADDefs

/-! Shared-kernel leaf A/D composition. The current physical word is an
actual exclusive-read result; it is never an initial owned-slot parameter. -/
namespace Xv6.Kernel.KptAD
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptShared.Capacity
abbrev Shares := SupervisorPteAD.Shares
abbrev Config := SupervisorPteAD.Config
abbrev Result := SupervisorPteAD.Result
abbrev program := SupervisorPteAD.program
abbrev enabled := SupervisorPteAD.enabled
abbrev footprint := SupervisorPteAD.footprint

abbrev cells {GF : BundledGFunctors} (capacity : Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  SupervisorPteAD.cells capacity.machine era cpu rs shares

noncomputable abbrev clients {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (era : Era.Record) (N : Namespace)
    (root : PtTree.PPN) (tree : PtTree.Tree) : IProp GF :=
  KptWriteEvent.clients capacity era N root tree

/-- The reread value is selected by the actual shared event; it may differ
in both A/D bits from the cached leaf and the persistent snapshot. -/
inductive Branch where
  | cached
  | disabled
  | reread (observed : BitVec 64)
  | written (observed new : BitVec 64)
  deriving DecidableEq

/-- These facts are derived by the implementation. In particular the caller
supplies neither an observed word nor a successful update equation. -/
def BranchFacts (cached reference : BitVec 64) (access : MemoryAccessType mem_payload)
    (adue : Bool) : Branch → Prop
  | .cached => update_PTE_Bits cached access = none
  | .disabled => (update_PTE_Bits cached access).isSome = true ∧ adue = false
  | .reread observed => (update_PTE_Bits cached access).isSome = true ∧ adue = true ∧
      PteCanonical.canon observed = PteCanonical.canon reference ∧
      update_PTE_Bits observed access = none
  | .written observed new => (update_PTE_Bits cached access).isSome = true ∧ adue = true ∧
      PteCanonical.canon observed = PteCanonical.canon reference ∧
      update_PTE_Bits observed access = some new ∧
      PteCanonical.canon new = PteCanonical.canon reference

def result : Branch → Result
  | .cached => .Ok (none, ())
  | .disabled => .Err (.PTW_PTE_Needs_Update (), ())
  | .reread observed => .Ok (some observed, ())
  | .written _ new => .Ok (some new, ())

def afterReservation (address : BitVec 64) (rr : Option Reservation) : Branch → Option Reservation
  | .cached | .disabled => rr
  | .reread observed => some (snapshot address 8 observed)
  | .written _ _ => none

/-- Only real memory events supply guards. Register prefixes still execute
through the native partial-footprint fold. -/
def guarded {GF : BundledGFunctors} (branch : Branch) (P : IProp GF) : IProp GF :=
  match branch with
  | .cached | .disabled => P
  | .reread _ => iprop(▷ P)
  | .written _ _ => iprop(▷ ▷ P)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def receipt (era : Era.Record) (cpu : CPU) (address : BitVec 64) : Branch → IProp GF
  | .cached | .disabled => iprop(emp)
  | .reread _ => iprop(∃ view : Nat,
      Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view)
  | .written _ new => iprop(∃ time : Nat, ⌜0 < time⌝ ∗
      Tso.History.logElem capacity.machine.era.history era.logEntries (time - 1)
        ⟨snapshot address 8 new, hartAgent cpu⟩ ∗
      Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) time)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def clientResources (era : Era.Record) (cpu : CPU) (rs : RegisterFile)
    (shares : Shares) (N : Namespace) (root : PtTree.PPN) (tree : PtTree.Tree)
    (address : BitVec 64) (rr : Option Reservation) (branch : Branch) : IProp GF :=
  iprop(cells capacity era cpu rs shares ∗ clients capacity era N root tree ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (afterReservation address rr branch) ∗ receipt capacity era cpu address branch)

/-- A genuine final continuation for every permitted branch. Branch facts
are inside its guards so the unknown shared reread value is chosen after
its actual event. This grants no guard to cached or disabled paths. -/
noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (tree : PtTree.Tree)
    (address cached reference : BitVec 64) (rr : Option Reservation)
    (access : MemoryAccessType mem_payload) (continuation : Result → SailM Unit)
    (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ branch : Branch, guarded branch iprop(
    ⌜BranchFacts cached reference access (enabled rs) branch⌝ -∗
    clientResources capacity era cpu rs shares N root tree address rr branch -∗
    MemoryWriteWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (continuation (result branch))) post))

end Xv6.Kernel.KptAD
