import Xv6.Kernel.MycpuKptFetchDefs
import Xv6.Kernel.MycpuKptBodyDefs
import Xv6.Kernel.MycpuActiveDefs

/-! One actual indexed shared-Sv39 cycle, on the same source packet.
The public final continuation retains the real fetch/body event guards,
clock-successor relation and restart guard. No body or fetch WP is input. -/
namespace Xv6.Kernel.MycpuKptCycle
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev Words := MycpuKptBody.Words
abbrev Tier := KernelDatum.Tier
abbrev entry := MycpuRegimeShell.entry
abbrev started := MycpuRegimeShell.started
abbrev Prepared := MycpuActive.prepared
abbrev footprint := MycpuRegimeShell.footprint
noncomputable abbrev packet := @MycpuRegimeShell.resources
abbrev code := @MycpuKptFetch.code
abbrev pair := @MycpuKptBody.pair

/-- Source hardware/delegation facts outside native msOwn/off ownership.
SIE=0 and every MsFacts conjunct are derived from the source packet. -/
structure Config (control : RegisterFile) : Prop where
  privilege : control .cur_privilege = .Supervisor
  active : control .hart_state = .HART_ACTIVE ()
  landing : control .elp = 0#1
  misa : control .misa = 0x800000000014112d#64
  environment : control .menvcfg = 0xa000000000000000#64
  delegated : control .mie &&& ~~~(control .mideleg) = 0#64
  pma : control .pma_regions = pmaBoot
  htif : control .htif_tohost_base = none

/-- Control/GPR updates after real decode/setNextPC and the actual body. -/
def bodyControl (i : Fin 14) (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile) : RegisterFile :=
  MycpuKptBody.afterControl (MycpuKptBody.route i) (Prepared i control) cpu values

def bodyValues (i : Fin 14) (control : RegisterFile) (cpu : CPU)
    (values : HartTp.GprFile) (words : Words) : HartTp.GprFile :=
  MycpuKptBody.afterValues (MycpuKptBody.route i) (Prepared i control) cpu values words

def bodyWords (i : Fin 14) (cpu : CPU) (values : HartTp.GprFile) (words : Words) : Words :=
  MycpuKptBody.afterWords (MycpuKptBody.route i) cpu values words

def nextPC (i : Fin 14) (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile) : BitVec 64 :=
  if i.val = 13 then MycpuReturn.retPC (HartTp.rget cpu values 1#5)
  else Sail.BitVec.addInt (control .PC) (MycpuDecode.width i)

abbrev Outcome (i : Fin 14) := MycpuKptBody.Outcome (MycpuKptBody.route i)

def afterReservation (i : Fin 14) (entrySP : BitVec 64) (rr : Option Reservation)
    (fetchTrace : List KptFetchHalf.Step) (outcome : Outcome i) : Option Reservation :=
  MycpuKptBody.afterReservation entrySP (KptFetchHalf.traceReservation rr fetchTrace) outcome

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Exact native Body.finish modal shape, with its continuation factored out.
The full observed memory facts stay under their actual A/D event guards. -/
def bodyGuards (r : MycpuKptBody.Route) (control : RegisterFile) (cpu : CPU)
    (values : HartTp.GprFile) (root : PtTree.PPN) (entrySP : BitVec 64)
    (next : MycpuKptBody.Outcome r → IProp GF) : IProp GF :=
  match r with
  | .registers instruction => next (.registers instruction)
  | .memory kind slot => MycpuKptMemory.guards (fun ppn data translation => iprop(
      ⌜KptMemory.CompletedFacts (entry control cpu values) data root kind
        (MycpuKptBody.slotAddress entrySP slot) ppn translation⌝ -∗
      ▷ (∀ view, next (.memory kind slot translation view))))

def guards (i : Fin 14) (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile)
    (root : PtTree.PPN) (entrySP : BitVec 64)
    (next : List KptFetchHalf.Step → Outcome i → IProp GF) : IProp GF :=
  KptFetch.guardChunks (entry control cpu values) root
    (KptFetch.chunks (MycpuDecode.address i) (MycpuKptFetch.result i)) (fun fetchTrace =>
      bodyGuards (MycpuKptBody.route i) (Prepared i control) cpu values root entrySP (next fetchTrace))

/-- All event receipts survive both the instruction body and restart. -/
def receipts (era : Era.Record) (cpu : CPU) (i : Fin 14) (entrySP : BitVec 64)
    (fetchTrace : List KptFetchHalf.Step) (outcome : Outcome i) : IProp GF :=
  iprop(KptFetchHalf.receipts capacity.translation era cpu fetchTrace ∗
    MycpuKptBody.receipts capacity era cpu entrySP outcome)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def activeResources (era : Era.Record) (cpu : CPU) (shares : Shares)
    (control : RegisterFile) (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN)
    (i : Fin 14) (tier : Tier) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (words : Words)
    (rr : Option Reservation) (fetchTrace : List KptFetchHalf.Step) (outcome : Outcome i)
    (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) (bodyControl i control cpu values)
      (bodyValues i control cpu values words) shares ∗ code capacity era tier ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    pair capacity era tier ξ entrySP (bodyWords i cpu values words) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (afterReservation i entrySP rr fetchTrace outcome) ∗
    receipts capacity era cpu i entrySP fetchTrace outcome ∗ frame)

noncomputable def activeFinish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (shares : Shares) (control : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (i : Fin 14)
    (tier : Tier) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (words : Words)
    (rr : Option Reservation) (frame : IProp GF) (continuation : Step → SailM Unit)
    (post : Empty → IProp GF) : IProp GF :=
  guards i control cpu values root entrySP (fun fetchTrace outcome => iprop(
    activeResources capacity era cpu shares control values N root i tier ξ entrySP words rr fetchTrace outcome frame -∗
    RegisterWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (continuation (.Step_Execute (.Retire_Success (),MycpuActive.instbits i)))) post))

/-- Returned cycle boundary: clocks may alter their three actual cells;
restart clears the actual reservation. All other resource columns remain. -/
noncomputable def cycleResources (era : Era.Record) (cpu : CPU) (shares : Shares)
    (control after : RegisterFile) (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN)
    (i : Fin 14) (tier : Tier) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (words : Words)
    (fetchTrace : List KptFetchHalf.Step) (outcome : Outcome i) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) after
      (bodyValues i (started control) cpu values words) shares ∗ code capacity era tier ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    pair capacity era tier ξ entrySP (bodyWords i cpu values words) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none ∗
    receipts capacity era cpu i entrySP fetchTrace outcome ∗ frame)

noncomputable def cycleFinish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (shares : Shares) (control : RegisterFile)
    (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN) (i : Fin 14)
    (tier : Tier) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (words : Words)
    (frame : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  guards i (started control) cpu values root entrySP (fun fetchTrace outcome => iprop(
    ∀ after, ⌜MycpuRegimeShell.Completed (bodyControl i (started control) cpu values) after⌝ -∗
      ▷ (∀ nextTick, cycleResources capacity era cpu shares control after values N root i tier ξ entrySP words
        fetchTrace outcome frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)))

end Xv6.Kernel.MycpuKptCycle
