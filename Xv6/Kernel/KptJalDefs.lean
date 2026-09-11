import Xv6.Kernel.MycpuKptCycleDefs

/-! Actual JAL x1 with arbitrary 21-bit immediate and general virtual PC.
Code owns the actual four-byte base instruction, including cross-page windows.
Immediate encodability follows from code alignment and the target-even premise. -/
namespace Xv6.Kernel.KptJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev Tier := KernelTextDatum.Tier
abbrev Config := MycpuKptCycle.Config
abbrev entry := MycpuRegimeShell.entry
abbrev started := MycpuRegimeShell.started
abbrev footprint := MycpuRegimeShell.footprint
noncomputable abbrev packet := @MycpuRegimeShell.resources

def instruction (imm : BitVec 21) : _root_.instruction := .JAL (imm,.Regidx 1#5)

/-- Standard JAL bit positions. The encoder cannot encode an odd immediate;
the eventual decoder law requires its low bit to be zero. -/
def encoding (imm : BitVec 21) : BitVec 32 :=
  BitVec.append (imm.extractLsb' 20 1)
    (BitVec.append (imm.extractLsb' 1 10)
      (BitVec.append (imm.extractLsb' 11 1)
        (BitVec.append (imm.extractLsb' 12 8) (BitVec.append 1#5 0x6f#7))))

def Encodable (imm : BitVec 21) : Prop := Sail.BitVec.access imm 0 = 0#1

def target (pc : BitVec 64) (imm : BitVec 21) : BitVec 64 := pc + sign_extend (m := 64) imm
def TargetEven (pc : BitVec 64) (imm : BitVec 21) : Prop := Sail.BitVec.access (target pc imm) 0 = 0#1
def link (pc : BitVec 64) : BitVec 64 := Sail.BitVec.addInt pc 4

def result (imm : BitVec 21) : FetchResult := .F_Base (encoding imm)

def prepared (pc : BitVec 64) (control : RegisterFile) : RegisterFile :=
  MachCSL.Sail.Registers.write control .nextPC (link pc)
def afterControl (pc : BitVec 64) (imm : BitVec 21) (control : RegisterFile) : RegisterFile :=
  MachCSL.Sail.Registers.write control .nextPC (target pc imm)
def afterValues (pc : BitVec 64) (values : HartTp.GprFile) : HartTp.GprFile :=
  HartTp.set values 1#5 (link pc)

/-- Same execute/ExecuteAs selector as actual run_hart_active. -/
def body [Platform] (imm : BitVec 21) : SailM ExecutionResult := do
  match ← execute (instruction imm) with
  | .ExecuteAs other => execute other
  | result => pure result

def executeTail [Platform] (imm : BitVec 21) : SailM Step := do
  let execution ← body imm
  pure (.Step_Execute (execution,encoding imm))

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Actual source base InstrBytes. Alignment comes from this resource;
there is no input decoder certificate or assumed successful fetch. -/
def code (era : Era.Record) (tier : Tier) (pc : BitVec 64) (imm : BitVec 21) : IProp GF :=
  KptFetch.instrBytes capacity.translation era tier pc (result imm)

/-- Full original fetch guard fold, with one or two independently mapped
chunks according to the general virtual PC. -/
def guards (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile)
    (root : PtTree.PPN) (pc : BitVec 64) (imm : BitVec 21)
    (next : List KptFetchHalf.Step → IProp GF) : IProp GF :=
  KptFetch.guardChunks (entry control cpu values) root (KptFetch.chunks pc (result imm)) next

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def fetchResources (era : Era.Record) (cpu : CPU) (shares : Shares)
    (control : RegisterFile) (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN)
    (tier : Tier) (ξ : TsoContext.CtxId) (pc : BitVec 64) (imm : BitVec 21)
    (rr : Option Reservation) (trace : List KptFetchHalf.Step) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) control values shares ∗ code capacity era tier pc imm ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu (KptFetchHalf.traceReservation rr trace) ∗
    KptFetchHalf.receipts capacity.translation era cpu trace ∗ frame)

noncomputable def fetchFinish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (shares : Shares) (control : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (tier : Tier) (ξ : TsoContext.CtxId) (pc : BitVec 64)
    (imm : BitVec 21) (rr : Option Reservation) (frame : IProp GF)
    (continuation : FetchResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  guards control cpu values root pc imm (fun trace => iprop(
    fetchResources capacity era cpu shares control values N root tier ξ pc imm rr trace frame -∗
    RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (result imm))) post))

noncomputable def bodyResources (era : Era.Record) (cpu : CPU) (shares : Shares) (control : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (ξ : TsoContext.CtxId) (pc : BitVec 64)
    (imm : BitVec 21) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) (afterControl pc imm control) (afterValues pc values) shares ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗ frame)

noncomputable def activeResources (era : Era.Record) (cpu : CPU) (shares : Shares) (control : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (tier : Tier) (ξ : TsoContext.CtxId) (pc : BitVec 64)
    (imm : BitVec 21) (rr : Option Reservation) (trace : List KptFetchHalf.Step) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) (afterControl pc imm control) (afterValues pc values) shares ∗
    code capacity era tier pc imm ∗ TsoContextReadWP.running capacity.machine era cpu ξ ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu (KptFetchHalf.traceReservation rr trace) ∗
    KptFetchHalf.receipts capacity.translation era cpu trace ∗ frame)

noncomputable def activeFinish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (shares : Shares) (control : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (tier : Tier) (ξ : TsoContext.CtxId) (pc : BitVec 64)
    (imm : BitVec 21) (rr : Option Reservation) (frame : IProp GF)
    (continuation : Step → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  guards control cpu values root pc imm (fun trace => iprop(
    activeResources capacity era cpu shares control values N root tier ξ pc imm rr trace frame -∗
    RegisterWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (continuation (.Step_Execute (.Retire_Success (),encoding imm)))) post))

noncomputable def cycleResources (era : Era.Record) (cpu : CPU) (shares : Shares) (after : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (tier : Tier) (ξ : TsoContext.CtxId) (pc : BitVec 64)
    (imm : BitVec 21) (trace : List KptFetchHalf.Step) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) after (afterValues pc values) shares ∗
    code capacity era tier pc imm ∗ TsoContextReadWP.running capacity.machine era cpu ξ ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none ∗
    KptFetchHalf.receipts capacity.translation era cpu trace ∗ frame)

noncomputable def cycleFinish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (shares : Shares) (control : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (tier : Tier) (ξ : TsoContext.CtxId) (pc : BitVec 64)
    (imm : BitVec 21) (frame : IProp GF)
    (post : Empty → IProp GF) : IProp GF :=
  guards (started control) cpu values root pc imm (fun trace => iprop(
    ∀ after, ⌜MycpuRegimeShell.Completed (afterControl pc imm (started control)) after⌝ -∗
      ▷ (∀ nextTick, cycleResources capacity era cpu shares after values N root tier ξ pc imm trace frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)))

end Xv6.Kernel.KptJal
