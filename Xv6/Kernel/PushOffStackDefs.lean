import Xv6.Kernel.PushOffCodeDefs
import Xv6.Kernel.MycpuKptMemoryDefs
import Xv6.Kernel.MycpuBareSourceDefs

namespace Xv6.Kernel.PushOffStack
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev Regime := MycpuRegimeShell.Regime
abbrev Tier := KernelDatum.Tier
abbrev Kind := KptMemory.Kind
abbrev File := HartTp.GprFile
abbrev Config := MycpuKptMemory.Config
abbrev entry := MycpuRegimeShell.entry
noncomputable abbrev packet := @MycpuRegimeShell.resources

inductive Slot where | ra | s0 | s1
  deriving DecidableEq

def index : Slot → HartTp.Index | .ra => 1#5 | .s0 => 8#5 | .s1 => 9#5
def register : Slot → Register | .ra => .x1 | .s0 => .x8 | .s1 => .x9
def regidx (slot : Slot) : _root_.regidx := .Regidx (index slot)
def ordinal : Slot → Nat | .ra => 1 | .s0 => 2 | .s1 => 3
def offset : Slot → BitVec 64 | .ra => 24#64 | .s0 => 16#64 | .s1 => 8#64
def immediate : Slot → BitVec 12 | .ra => 24#12 | .s0 => 16#12 | .s1 => 8#12

def instructionIndex : Kind → Slot → PushOffCode.Index
  | .store, .ra => ⟨1, by decide⟩ | .store, .s0 => ⟨2, by decide⟩ | .store, .s1 => ⟨3, by decide⟩
  | .load, .ra => ⟨14, by decide⟩ | .load, .s0 => ⟨15, by decide⟩ | .load, .s1 => ⟨16, by decide⟩

def body [Platform] (kind : Kind) (slot : Slot) : SailM ExecutionResult :=
  execute (PushOffCode.normalized (instructionIndex kind slot))
def sourceValue (cpu : CPU) (values : File) (slot : Slot) : BitVec 64 := HartTp.rget cpu values (index slot)
def address (cpu : CPU) (values : File) (slot : Slot) : BitVec 64 := HartTp.rget cpu values 2#5 + offset slot

def storeTail : KptMemory.Result .store → SailM ExecutionResult
  | .Ok _ => pure (.Retire_Success ())
  | .Err error => pure error

def loadTail (slot : Slot) : KptMemory.Result .load → SailM ExecutionResult
  | .Ok word => do
      wX_bits (regidx slot) word
      pure (.Retire_Success ())
  | .Err error => pure error

def afterMap : Kind → Slot → File → BitVec 64 → File
  | .store, _, values, _ => values
  | .load, slot, values, word => HartTp.set values (index slot) word

def physicalAfter (kind : Kind) (slot : Slot) (rs : RegisterFile) (word : BitVec 64) : RegisterFile :=
  match kind, slot with
  | .store, _ => rs
  | .load, .ra => MachCSL.Sail.Registers.write rs .x1 word
  | .load, .s0 => MachCSL.Sail.Registers.write rs .x8 word
  | .load, .s1 => MachCSL.Sail.Registers.write rs .x9 word

abbrev memoryShares := MycpuKptMemory.memoryShares
def footprint (s : Shares) (slot : Slot) : RegisterFootprint.Footprint :=
  KptAddress.auxiliaryFootprint (memoryShares s) ++ [(.x2, .own 1), (register slot, .own 1)]
def remainderFootprint (s : Shares) (slot : Slot) : RegisterFootprint.Footprint :=
  (MycpuRegimeShell.footprint s).filter (fun cell => !((footprint s slot).map Prod.fst).contains cell.1)
def bareFootprint (s : Shares) (slot : Slot) : RegisterFootprint.Footprint :=
  footprint s slot ++ [(.satp, .own 1), (.pmpcfg_n, .own 1), (.pmpaddr_n, .own 1)]

abbrev Words := Slot → BitVec 64
def afterWords (kind : Kind) (slot : Slot) (cpu : CPU) (values : File) (words : Words) : Words :=
  match kind with
  | .load => words
  | .store => fun other => if other = slot then sourceValue cpu values slot else words other

def StackReady (cpu : CPU) (values : File) (entrySP : BitVec 64) : Prop :=
  HartTp.rget cpu values 2#5 = entrySP - 32#64

def Outcome : Regime → Type
  | .bare => Unit
  | .kpt _ _ => KptAddress.Outcome

def afterReservation (regime : Regime) (kind : Kind) (va : BitVec 64) (rr : Option Reservation) :
    Outcome regime → Option Reservation :=
  match regime, kind with
  | .bare, .load => fun _ => rr
  | .bare, .store => fun _ => none
  | .kpt _ _, _ => KptMemory.afterReservation kind va rr

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Three actual saved words; the fourth frame word is kept separately. -/
def savedWords (era : Era.Record) (tier : Tier) (ξ : TsoContext.CtxId)
    (entrySP : BitVec 64) (words : Words) : IProp GF :=
  iprop(KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk entrySP 1) (.own 1) (words .ra) ∗
    KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk entrySP 2) (.own 1) (words .s0) ∗
    KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk entrySP 3) (.own 1) (words .s1))

/-- Mapping claims remain in this closing wand and accept the actual newly
written physical context bytes and timestamps. -/
def closeIdentity (era : Era.Record) (ξ : TsoContext.CtxId) (va : BitVec 64) : IProp GF :=
  iprop(∀ newWord, TsoContextReadWP.wordPointsto capacity.machine era ξ va (.own 1) newWord -∗
    KernelDatum.word capacity.translation era .identity ξ va (.own 1) newWord)

def receipts (era : Era.Record) (cpu : CPU) (regime : Regime) (va : BitVec 64) : Outcome regime → IProp GF :=
  match regime with
  | .bare => fun _ => iprop(emp)
  | .kpt _ _ => KptAddress.receipts capacity.translation era cpu va

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def resources (era : Era.Record) (cpu : CPU) (regime : Regime)
    (control : RegisterFile) (values : File) (s : Shares) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (old : BitVec 64) (rr : Option Reservation)
    (outcome : Outcome regime) (view : Nat) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu regime control (afterMap kind slot values old) s ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    KernelDatum.word capacity.translation era tier ξ (address cpu values slot) (.own 1)
      (KptMemory.valueAfter kind old (sourceValue cpu values slot)) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (afterReservation regime kind (address cpu values slot) rr outcome) ∗
    receipts capacity era cpu regime (address cpu values slot) outcome ∗
    Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view ∗ frame)

/-- One real data-event guard, preceded by precisely the KPT translation
branch guards when the actual regime is KPT. All observations are bound
inside their branch; no branch-success or physical restoration oracle. -/
noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (regime : Regime)
    (control : RegisterFile) (values : File) (s : Shares) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (old : BitVec 64) (rr : Option Reservation)
    (frame : IProp GF) (continuation : ExecutionResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  match regime with
  | .bare => iprop(▷ (∀ view,
      resources capacity era cpu .bare control values s kind slot tier ξ old rr () view frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (continuation (.Retire_Success ()))) post))
  | .kpt N root => MycpuKptMemory.guards (fun ppn data outcome =>
      iprop(⌜KptMemory.CompletedFacts (entry control cpu values) data root kind (address cpu values slot) ppn outcome⌝ -∗
        ▷ (∀ view, resources capacity era cpu (.kpt N root) control values s kind slot tier ξ old rr outcome view frame -∗
          RegisterWP.threadWP capacity.machine image fixed whole
            (.hart gen cpu (continuation (.Retire_Success ()))) post)))

end Xv6.Kernel.PushOffStack
