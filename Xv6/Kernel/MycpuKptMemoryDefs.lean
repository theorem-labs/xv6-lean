import Xv6.Kernel.MycpuRegimeShellDefs
import Xv6.Kernel.KptMemoryDefs

/-! The four actual compressed SP-relative mycpu bodies over shared Sv39.
The common cycle packet supplies all operands and controls exactly once.
This layer starts at decoded execution, not fetch, dispatch or retirement. -/
namespace Xv6.Kernel.MycpuKptMemory
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev Slot := MycpuMemory.Slot
abbrev Kind := KptMemory.Kind
abbrev Tier := KernelDatum.Tier
abbrev entry := MycpuRegimeShell.entry
noncomputable abbrev packet := @MycpuRegimeShell.resources

def index : Slot → HartTp.Index | .ra => 1#5 | .s0 => 8#5
def sourceValue (cpu : CPU) (values : HartTp.GprFile) (slot : Slot) : BitVec 64 :=
  HartTp.rget cpu values (index slot)
def address (cpu : CPU) (values : HartTp.GprFile) (slot : Slot) : BitVec 64 :=
  HartTp.rget cpu values 2#5 + MycpuMemory.offset slot

def memoryShares (s : Shares) : KptMemory.Shares :=
  ⟨.own 1, s.privilege, s.pma, s.htif, s.environment⟩
def footprint (s : Shares) (slot : Slot) : RegisterFootprint.Footprint :=
  KptAddress.auxiliaryFootprint (memoryShares s) ++
    [(.x2, .own 1), (MycpuMemory.dataRegister slot, .own 1)]
def remainderFootprint (s : Shares) (slot : Slot) : RegisterFootprint.Footprint :=
  (MycpuRegimeShell.footprint s).filter
    (fun cell => !((footprint s slot).map Prod.fst).contains cell.1)

/-- The remaining actual hardware facts. Source msOwn supplies MPRV/MXR/SXL;
no translated address, successful memory response or physical word is given. -/
structure Config (control : RegisterFile) : Prop where
  privilege : control .cur_privilege = .Supervisor
  pma : control .pma_regions = pmaBoot
  htif : control .htif_tohost_base = none
  pmm : pmm_mode_backwards (_get_MEnvcfg_PMM (control .menvcfg)) = .PMM_Disabled
  adue : _get_MEnvcfg_ADUE (control .menvcfg) = 1#1

def body [Platform] : Kind → Slot → SailM ExecutionResult
  | .store, slot => MycpuMemory.storeBody slot
  | .load, slot => MycpuMemory.loadBody slot

def instructionIndex : Kind → Slot → Fin 14
  | .store, slot => MycpuMemory.storeIndex slot
  | .load, slot => MycpuMemory.loadIndex slot

/-- Actual STORE ignores the Boolean on both success arms. Its error result
is returned verbatim. Native RAM ownership later proves the true arm. -/
def storeTail : KptMemory.Result .store → SailM ExecutionResult
  | .Ok _ => pure (.Retire_Success ())
  | .Err error => pure error

def loadTail (slot : Slot) : KptMemory.Result .load → SailM ExecutionResult
  | .Ok word => MycpuMemory.loadTail slot word
  | .Err error => pure error

def tail (kind : Kind) (slot : Slot) : KptMemory.Result kind → SailM ExecutionResult :=
  match kind with | .load => loadTail slot | .store => storeTail

def afterMap : Kind → Slot → HartTp.GprFile → BitVec 64 → HartTp.GprFile
  | .store, _, values, _ => values
  | .load, slot, values, old => HartTp.set values (index slot) old

def otherSlot : Slot → Slot | .ra => .s0 | .s0 => .ra

abbrev Pair := Slot → BitVec 64
def afterPair (kind : Kind) (slot : Slot) (cpu : CPU) (values : HartTp.GprFile) (words : Pair) : Pair :=
  match kind with
  | .load => words
  | .store => fun other => if other = slot then sourceValue cpu values slot else words other

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- The two virtual save words at current SP+8 and SP. No physical word or
global no-wrap premise replaces their actual tier/context ownership. -/
def pair (era : Era.Record) (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId)
    (values : HartTp.GprFile) (words : Pair) : IProp GF :=
  iprop(KernelDatum.word capacity.translation era tier ξ (address cpu values .ra) (.own 1) (words .ra) ∗
    KernelDatum.word capacity.translation era tier ξ (address cpu values .s0) (.own 1) (words .s0))

/-- The other forty-three physical registers, unchanged source bit resources,
and software x0 fact while the seven-cell memory packet is borrowed. -/
def packetFrame (era : Era.Record) (cpu : CPU) (control : RegisterFile)
    (values : HartTp.GprFile) (shares : Shares) (slot : Slot) : IProp GF :=
  iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry control cpu values) (remainderFootprint shares slot) ∗
    MycpuRegimeShell.bitFrame capacity era cpu (control .mstatus) ∗ ⌜values 0#5 = 0#64⌝)

/-- The same hit/miss and A/D guard nesting as the actual KptMemory rule.
The final guard is the ordinary data event; all witnesses are scoped inside
their actual branches rather than supplied as successful-response premises. -/
def guards (next : PtTree.PPN → KptAddress.Data → KptAddress.Outcome → IProp GF) : IProp GF :=
  iprop(∀ ppn data tree p2 p1 referenceA referenceD,
    (∀ a d update, KptAD.guarded update
      (next ppn data (.translated tree p2 p1 referenceA referenceD (.hit a d update)))) ∧
    ▷ ▷ ▷ (∀ a d view2 view1 view0 update, KptAD.guarded update
      (next ppn data (.translated tree p2 p1 referenceA referenceD (.miss a d view2 view1 view0 update)))))

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def resources (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : HartTp.GprFile)
    (shares : Shares) (N : Namespace) (root : PtTree.PPN) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 64) (rr : Option Reservation)
    (outcome : KptAddress.Outcome) (view : Nat) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) control (afterMap kind slot values old) shares ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    KernelDatum.word capacity.translation era tier ξ (address cpu values slot) dq
      (KptMemory.valueAfter kind old (sourceValue cpu values slot)) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (KptMemory.afterReservation kind (address cpu values slot) rr outcome) ∗
    KptAddress.receipts capacity.translation era cpu (address cpu values slot) outcome ∗
    Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view ∗ frame)

noncomputable def continueWith [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : HartTp.GprFile)
    (shares : Shares) (N : Namespace) (root : PtTree.PPN) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 64) (rr : Option Reservation)
    (frame : IProp GF) (continuation : ExecutionResult → SailM Unit) (post : Empty → IProp GF) (ppn : PtTree.PPN) (data : KptAddress.Data) (outcome : KptAddress.Outcome) : IProp GF :=
  iprop(
    ⌜KptMemory.CompletedFacts (entry control cpu values) data root kind (address cpu values slot) ppn outcome⌝ -∗
    ▷ (∀ view, resources capacity era cpu control values shares N root kind slot tier ξ dq old rr outcome view frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (continuation (.Retire_Success ()))) post))

noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : HartTp.GprFile)
    (shares : Shares) (N : Namespace) (root : PtTree.PPN) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 64) (rr : Option Reservation)
    (frame : IProp GF) (continuation : ExecutionResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  guards (continueWith capacity image fixed whole gen era cpu control values shares N root kind slot tier ξ dq old rr frame continuation post)

noncomputable def pairResources (era : Era.Record) (cpu : CPU) (control : RegisterFile)
    (values : HartTp.GprFile) (shares : Shares) (N : Namespace) (root : PtTree.PPN)
    (kind : Kind) (slot : Slot) (tier : Tier) (ξ : TsoContext.CtxId) (words : Pair)
    (rr : Option Reservation) (outcome : KptAddress.Outcome) (view : Nat) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) control (afterMap kind slot values (words slot)) shares ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    pair capacity era cpu tier ξ values (afterPair kind slot cpu values words) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (KptMemory.afterReservation kind (address cpu values slot) rr outcome) ∗
    KptAddress.receipts capacity.translation era cpu (address cpu values slot) outcome ∗
    Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view ∗ frame)

noncomputable def continuePair [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : HartTp.GprFile)
    (shares : Shares) (N : Namespace) (root : PtTree.PPN) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (words : Pair) (rr : Option Reservation)
    (frame : IProp GF) (continuation : ExecutionResult → SailM Unit) (post : Empty → IProp GF) (ppn : PtTree.PPN) (data : KptAddress.Data) (outcome : KptAddress.Outcome) : IProp GF :=
  iprop(⌜KptMemory.CompletedFacts (entry control cpu values) data root kind (address cpu values slot) ppn outcome⌝ -∗
    ▷ (∀ view, pairResources capacity era cpu control values shares N root kind slot tier ξ words rr outcome view frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (continuation (.Retire_Success ()))) post))

noncomputable def finishPair [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : HartTp.GprFile)
    (shares : Shares) (N : Namespace) (root : PtTree.PPN) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (words : Pair) (rr : Option Reservation)
    (frame : IProp GF) (continuation : ExecutionResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  guards (continuePair capacity image fixed whole gen era cpu control values shares N root kind slot tier ξ words rr frame continuation post)

end Xv6.Kernel.MycpuKptMemory
