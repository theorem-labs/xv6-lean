import Xv6.Kernel.PushOffWord4BareDefs
import Xv6.Kernel.MycpuKptMemoryDefs
import Xv6.Kernel.PushOffCodeDefs
import Xv6.Kernel.MycpuBareSourceDefs

/-! Normalized word bodies for exactly source rows 8/11/13/22. Fetch,
compressed expansion, cycle retirement and the enclosing function are separate. -/
namespace Xv6.Kernel.PushOffWord4
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev File := HartTp.GprFile
abbrev Regime := MycpuRegimeShell.Regime
abbrev Kind := KptMemory4.Kind
abbrev Tier := KernelDatum.Tier
abbrev entry := MycpuRegimeShell.entry
noncomputable abbrev packet := @MycpuRegimeShell.resources

inductive Op where
  | loadFirst | loadAgain | storeNoff | storeIntena
  deriving DecidableEq

def index : Op → PushOffCode.Index
  | .loadFirst => ⟨8, by decide⟩
  | .loadAgain => ⟨11, by decide⟩
  | .storeNoff => ⟨13, by decide⟩
  | .storeIntena => ⟨22, by decide⟩
def kind : Op → Kind
  | .loadFirst | .loadAgain => .load
  | .storeNoff | .storeIntena => .store
def immediate : Op → BitVec 12
  | .storeIntena => 124#12
  | _ => 120#12
def offset (op : Op) : BitVec 64 := (immediate op).signExtend 64
def address (cpu : CPU) (values : File) (op : Op) : BitVec 64 :=
  HartTp.rget cpu values 10#5 + offset op
def sourceValue (cpu : CPU) (values : File) : BitVec 32 :=
  (HartTp.rget cpu values 15#5).setWidth 32

def body [Platform] (op : Op) : SailM ExecutionResult :=
  execute (PushOffCode.normalized (index op))
def loadTail : KptMemory4.Result .load → SailM ExecutionResult
  | .Ok word => do
      wX_bits (.Regidx 15#5) (word.signExtend 64)
      pure (.Retire_Success ())
  | .Err error => pure error
def storeTail : KptMemory4.Result .store → SailM ExecutionResult
  | .Ok _ => pure (.Retire_Success ())
  | .Err error => pure error
def tail (op : Op) : KptMemory4.Result (kind op) → SailM ExecutionResult :=
  match op with
  | .loadFirst | .loadAgain => loadTail
  | .storeNoff | .storeIntena => storeTail

def factored [Platform] (op : Op) : SailM ExecutionResult :=
  match op with
  | .loadFirst | .loadAgain => do
      let base ← rX_bits (.Regidx 10#5)
      KptMemory4.program .load (base + offset op) 0#32 >>= loadTail
  | .storeNoff | .storeIntena => do
      let value ← rX_bits (.Regidx 15#5)
      let base ← rX_bits (.Regidx 10#5)
      KptMemory4.program .store (base + offset op) (value.setWidth 32) >>= storeTail

def afterMap (op : Op) (values : File) (old : BitVec 32) : File :=
  match kind op with
  | .load => HartTp.set values 15#5 (old.signExtend 64)
  | .store => values

def memoryShares (s : Shares) : KptMemory4.Shares :=
  ⟨.own 1, s.privilege, s.pma, s.htif, s.environment⟩
def footprint (s : Shares) : RegisterFootprint.Footprint :=
  KptAddress.auxiliaryFootprint (memoryShares s) ++ [(.x10, .own 1), (.x15, .own 1)]
def remainderFootprint (s : Shares) : RegisterFootprint.Footprint :=
  (MycpuRegimeShell.footprint s).filter (fun cell => !((footprint s).map Prod.fst).contains cell.1)
def bareShares (s : Shares) : PushOffWord4Bare.Shares :=
  ⟨⟨⟨.own 1, s.privilege, .own 1⟩, ⟨s.pma, .own 1, .own 1, s.htif⟩⟩, s.environment⟩
def bareFootprint (s : Shares) : RegisterFootprint.Footprint :=
  PushOffWord4Bare.footprint (bareShares s) ++ [(.x10, .own 1), (.x15, .own 1)]
def fullBareFootprint (s : Shares) : RegisterFootprint.Footprint :=
  MycpuRegimeShell.footprint s ++ [(.satp,.own 1),(.pmpcfg_n,.own 1),(.pmpaddr_n,.own 1)]

/-- Controls are explicit owned hardware configuration. Bare does not need
ADUE; the shared translation route does. MsFacts comes from the packet. -/
structure Config (regime : Regime) (control : RegisterFile) : Prop where
  privilege : control .cur_privilege = .Supervisor
  pma : control .pma_regions = pmaBoot
  htif : control .htif_tohost_base = none
  pmm : pmm_mode_backwards (_get_MEnvcfg_PMM (control .menvcfg)) = .PMM_Disabled
  adue : ∀ N root, regime = .kpt N root → _get_MEnvcfg_ADUE (control .menvcfg) = 1#1

/-- Only KPT execution can return a translation outcome. Bare preserves rr
on a load; every ordinary store clears it. -/
def Outcome : Regime → Type
  | .bare => Unit
  | .kpt _ _ => KptAddress.Outcome

def afterReservation (regime : Regime) (op : Op) (va : BitVec 64)
    (rr : Option Reservation) : Outcome regime → Option Reservation :=
  match regime with
  | .bare => fun _ => PushOffWord4Bare.afterReservation (kind op) rr
  | .kpt _ _ => fun outcome => KptMemory4.afterReservation (kind op) va rr outcome

variable {GF : BundledGFunctors} (capacity : Capacity GF)
def packetFrame (era : Era.Record) (cpu : CPU) (control : RegisterFile)
    (values : File) (shares : Shares) : IProp GF :=
  iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry control cpu values) (remainderFootprint shares) ∗
    MycpuRegimeShell.bitFrame capacity era cpu (control .mstatus) ∗ ⌜values 0#5 = 0#64⌝)

/-- The exact fifty-three keys when the supplied Bare resource is opened.
Only the three existentially owned translation projections are patched. -/
def barePacket (era : Era.Record) (cpu : CPU) (control : RegisterFile)
    (values : File) (shares : Shares) : IProp GF :=
  iprop(∃ (satp : BitVec 64) (pmp : RegisterFile),
    ⌜_get_Satp64_Mode (Mk_Satp64 satp) = 0#4 ∧ MachCSL.Machine.SupervisorPmp.TorRam pmp⌝ ∗
    RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry (MycpuBareSource.patch control satp pmp) cpu values) (fullBareFootprint shares) ∗
    MycpuRegimeShell.bitFrame capacity era cpu (control .mstatus) ∗ ⌜values 0#5 = 0#64⌝)

variable {hlc : HasLC} [InvGS_gen hlc GF]
noncomputable def receipts (era : Era.Record) (cpu : CPU) (va : BitVec 64)
    (regime : Regime) : Outcome regime → IProp GF :=
  match regime with
  | .bare => fun _ => iprop(emp)
  | .kpt _ _ => fun outcome => KptAddress.receipts capacity.translation era cpu va outcome

noncomputable def resources (era : Era.Record) (cpu : CPU) (regime : Regime)
    (control : RegisterFile) (values : File) (shares : Shares) (op : Op) (tier : Tier)
    (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 32) (rr : Option Reservation)
    (outcome : Outcome regime) (view : Nat) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu regime control (afterMap op values old) shares ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    KernelDatumWord4.word capacity.translation era tier ξ (address cpu values op) dq
      (KptMemory4.valueAfter (kind op) old (sourceValue cpu values)) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (afterReservation regime op (address cpu values op) rr outcome) ∗
    receipts capacity era cpu (address cpu values op) regime outcome ∗
    Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view ∗ frame)

/-- Internal memory boundary before the actual load destination write. -/
noncomputable def memoryResources (era : Era.Record) (cpu : CPU) (regime : Regime)
    (control : RegisterFile) (values : File) (shares : Shares) (op : Op) (tier : Tier)
    (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 32) (rr : Option Reservation)
    (outcome : Outcome regime) (view : Nat) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu regime control values shares ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    KernelDatumWord4.word capacity.translation era tier ξ (address cpu values op) dq
      (KptMemory4.valueAfter (kind op) old (sourceValue cpu values)) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (afterReservation regime op (address cpu values op) rr outcome) ∗
    receipts capacity era cpu (address cpu values op) regime outcome ∗
    Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view ∗ frame)

/-- KPT witnesses and their facts remain inside the original branch guards;
Bare has exactly the ordinary data-event guard. -/
noncomputable def guards (regime : Regime) (rs : RegisterFile) (op : Op) (va : BitVec 64)
    (next : Outcome regime → Nat → IProp GF) : IProp GF :=
  match regime with
  | .bare => iprop(▷ ∀ view, next () view)
  | .kpt _ root => MycpuKptMemory.guards (fun ppn data outcome =>
      iprop(⌜KptMemory4.CompletedFacts rs data root (kind op) va ppn outcome⌝ -∗
        ▷ ∀ view, next outcome view))

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (regime : Regime) (control : RegisterFile) (values : File) (shares : Shares)
    (op : Op) (tier : Tier) (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 32)
    (rr : Option Reservation) (frame : IProp GF) (continuation : ExecutionResult → SailM Unit)
    (post : Empty → IProp GF) : IProp GF :=
  guards regime (entry control cpu values) op (address cpu values op) (fun outcome view =>
    iprop(resources capacity era cpu regime control values shares op tier ξ dq old rr outcome view frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (continuation (.Retire_Success ()))) post))
noncomputable def memoryFinish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (regime : Regime) (control : RegisterFile) (values : File) (shares : Shares)
    (op : Op) (tier : Tier) (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 32)
    (rr : Option Reservation) (frame : IProp GF) (continuation : KptMemory4.Result (kind op) → SailM Unit)
    (post : Empty → IProp GF) : IProp GF :=
  guards regime (entry control cpu values) op (address cpu values op) (fun outcome view =>
    iprop(memoryResources capacity era cpu regime control values shares op tier ξ dq old rr outcome view frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (continuation (KptMemory4.result (kind op) old))) post))

end Xv6.Kernel.PushOffWord4
