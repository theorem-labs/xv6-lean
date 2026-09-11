import Xv6.Kernel.MycpuKptRegisterDefs
import Xv6.Kernel.MycpuKptMemoryDefs

/-! All fourteen actual decoded bodies with one fixed virtual save area.
The save-area anchor is entrySP−16 and is never reindexed by a scalar SP update.
Fetch, retirement and the complete function's phase invariant are separate. -/
namespace Xv6.Kernel.MycpuKptBody
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev Words := MycpuKptMemory.Pair
abbrev Slot := MycpuMemory.Slot
abbrev Kind := KptMemory.Kind
abbrev entry := MycpuRegimeShell.entry
noncomputable abbrev packet := @MycpuRegimeShell.resources

inductive Route where
  | registers (instruction : MycpuKptRegister.Instruction)
  | memory (kind : Kind) (slot : Slot)

def route (i : Fin 14) : Route :=
  match i.val with
  | 0 => .registers (.scalar ⟨0, by decide⟩)
  | 1 => .memory .store .ra
  | 2 => .memory .store .s0
  | 3 => .registers (.scalar ⟨1, by decide⟩)
  | 4 => .registers (.scalar ⟨2, by decide⟩)
  | 5 => .registers (.scalar ⟨3, by decide⟩)
  | 6 => .registers (.scalar ⟨4, by decide⟩)
  | 7 => .registers (.scalar ⟨5, by decide⟩)
  | 8 => .registers (.scalar ⟨6, by decide⟩)
  | 9 => .registers (.scalar ⟨7, by decide⟩)
  | 10 => .memory .load .ra
  | 11 => .memory .load .s0
  | 12 => .registers (.scalar ⟨8, by decide⟩)
  | _ => .registers .returns

def routeIndex : Route → Fin 14
  | .registers instruction => MycpuKptRegister.index instruction
  | .memory kind slot => MycpuKptMemory.instructionIndex kind slot

def routedBody [Platform] : Route → SailM ExecutionResult
  | .registers instruction => MycpuKptRegister.body instruction
  | .memory kind slot => MycpuKptMemory.body kind slot

def body [Platform] (i : Fin 14) : SailM ExecutionResult := do
  match ← execute (MycpuDecode.decoded i) with
  | .ExecuteAs other => execute other
  | result => pure result

def anchor (entrySP : BitVec 64) : BitVec 64 := entrySP - 16#64
def slotAddress (entrySP : BitVec 64) (slot : Slot) : BitVec 64 :=
  anchor entrySP + MycpuMemory.offset slot

/-- Only memory bodies need the current-SP/save-area equality. -/
def StackReady (i : Fin 14) (entrySP : BitVec 64) (cpu : CPU) (values : HartTp.GprFile) : Prop :=
  match route i with
  | .registers _ => True
  | .memory _ _ => HartTp.rget cpu values 2#5 = anchor entrySP

def Config (i : Fin 14) (control : RegisterFile) : Prop :=
  match route i with
  | .registers instruction => MycpuKptRegister.Config instruction control
  | .memory _ _ => MycpuKptMemory.Config control

def afterValues (r : Route) (control : RegisterFile) (cpu : CPU)
    (values : HartTp.GprFile) (words : Words) : HartTp.GprFile :=
  match r with
  | .registers instruction => MycpuKptRegister.afterValues instruction control cpu values
  | .memory kind slot => MycpuKptMemory.afterMap kind slot values (words slot)

def afterControl (r : Route) (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile) : RegisterFile :=
  match r with
  | .registers instruction => MycpuKptRegister.afterControl instruction control cpu values
  | .memory _ _ => control

def afterWords (r : Route) (cpu : CPU) (values : HartTp.GprFile) (words : Words) : Words :=
  match r with
  | .registers _ => words
  | .memory kind slot => MycpuKptMemory.afterPair kind slot cpu values words

/-- The source stack-pointer boundary schedule, separate from the weaker
memory-only premise needed by the body WP. -/
def phaseSP (i : Fin 14) (entrySP : BitVec 64) : BitVec 64 :=
  if i.val = 0 ∨ i.val = 13 then entrySP else anchor entrySP

def nextSP (i : Fin 14) (entrySP : BitVec 64) : BitVec 64 :=
  if i.val = 0 then anchor entrySP else if i.val = 12 then entrySP else phaseSP i entrySP

/-- Impossible register/memory outcome combinations are excluded by the index. -/
inductive Outcome : Route → Type where
  | registers (instruction : MycpuKptRegister.Instruction) : Outcome (.registers instruction)
  | memory (kind : Kind) (slot : Slot) (translation : KptAddress.Outcome) (view : Nat) : Outcome (.memory kind slot)

def afterReservation (entrySP : BitVec 64) (rr : Option Reservation) {r : Route} : Outcome r → Option Reservation
  | .registers _ => rr
  | .memory kind slot translation _ => KptMemory.afterReservation kind (slotAddress entrySP slot) rr translation

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def pair (era : Era.Record) (tier : KernelDatum.Tier) (ξ : TsoContext.CtxId)
    (entrySP : BitVec 64) (words : Words) : IProp GF :=
  iprop(KernelDatum.word capacity.translation era tier ξ (slotAddress entrySP .ra) (.own 1) (words .ra) ∗
    KernelDatum.word capacity.translation era tier ξ (slotAddress entrySP .s0) (.own 1) (words .s0))

def receipts (era : Era.Record) (cpu : CPU) (entrySP : BitVec 64) {r : Route} : Outcome r → IProp GF
  | .registers _ => iprop(True)
  | .memory _ slot translation view => iprop(
      KptAddress.receipts capacity.translation era cpu (slotAddress entrySP slot) translation ∗
      Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def resources (era : Era.Record) (cpu : CPU) (shares : Shares) (control : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (r : Route)
    (tier : KernelDatum.Tier) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (words : Words)
    (rr : Option Reservation) (outcome : Outcome r) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) (afterControl r control cpu values)
      (afterValues r control cpu values words) shares ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    pair capacity era tier ξ entrySP (afterWords r cpu values words) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu (afterReservation entrySP rr outcome) ∗
    receipts capacity era cpu entrySP outcome ∗ frame)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (shares : Shares) (control : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (r : Route)
    (tier : KernelDatum.Tier) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (words : Words)
    (rr : Option Reservation) (frame : IProp GF) (continuation : ExecutionResult → SailM Unit)
    (post : Empty → IProp GF) : IProp GF :=
  match r with
  | .registers instruction => iprop(
      resources capacity era cpu shares control values N root (.registers instruction)
        tier ξ entrySP words rr (.registers instruction) frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post)
  | .memory kind slot => MycpuKptMemory.guards (fun ppn data translation => iprop(
      ⌜KptMemory.CompletedFacts (entry control cpu values) data root kind (slotAddress entrySP slot) ppn translation⌝ -∗
      ▷ (∀ view, resources capacity era cpu shares control values N root (.memory kind slot)
        tier ξ entrySP words rr (.memory kind slot translation view) frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post)))

end Xv6.Kernel.MycpuKptBody
