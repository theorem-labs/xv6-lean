import Xv6.Kernel.MycpuKptCycleDefs
import Xv6.Kernel.MycpuRegisterSequenceDefs
import Xv6.Kernel.SieOffPacketDefs

/-! Full-function resource/result boundary for the actual fourteen shared-KPT
cycles. Phase is internal pure bookkeeping, not an executable replacement or
an assumed instruction/translation success predicate. -/
namespace Xv6.Kernel.MycpuKpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuKptCycle.Capacity
abbrev Shares := MycpuKptCycle.Shares
abbrev Words := MycpuKptCycle.Words
abbrev entry := MycpuRegimeShell.entry
noncomputable abbrev packet := @MycpuRegimeShell.resources
abbrev code := @MycpuKptCycle.code
abbrev pair := @MycpuKptBody.pair
abbrev Config := MycpuKptCycle.Config

def entrySP (cpu : CPU) (original : HartTp.GprFile) : BitVec 64 := HartTp.rget cpu original 2#5

def savedWords (cpu : CPU) (original : HartTp.GprFile) : Words
  | .ra => HartTp.rget cpu original 1#5
  | .s0 => HartTp.rget cpu original 8#5

/-- The words become known only after their actual indexed store rules. -/
def wordsAt (cpu : CPU) (original : HartTp.GprFile) (old : Words) (k : Nat) : Words
  | .ra => if k ≤ 1 then old .ra else savedWords cpu original .ra
  | .s0 => if k ≤ 2 then old .s0 else savedWords cpu original .s0

/-- Actual restart clears the reservation after each completed cycle. -/
def reservationAt (initial : Option Reservation) (k : Nat) : Option Reservation :=
  if k = 0 then initial else none

/-- Every successor permits precisely the arbitrary clock values described by
Completed. The pure relation is constructed inside the native cycle proof. -/
inductive Phase (initial : RegisterFile) (original : HartTp.GprFile) (old : Words) (cpu : CPU) :
    Nat → RegisterFile → HartTp.GprFile → Words → Prop where
  | zero : Phase initial original old cpu 0 initial original old
  | next {k before values words after} (bound : k < 14)
      (phase : Phase initial original old cpu k before values words)
      (done : MycpuRegimeShell.Completed
        (MycpuKptCycle.bodyControl ⟨k,bound⟩ (MycpuKptCycle.started before) cpu values) after) :
      Phase initial original old cpu (k+1) after
        (MycpuKptCycle.bodyValues ⟨k,bound⟩ (MycpuKptCycle.started before) cpu values words)
        (MycpuKptCycle.bodyWords ⟨k,bound⟩ cpu values words)

/-- Only physically owned non-clock control columns are exported as stable.
SATP/TLB/PMP remain existentially folded inside the KPT residue. -/
def stableControls : List Register :=
  [.mstatus, .cur_privilege, .misa, .mie, .mideleg, .menvcfg, .elp,
   .pma_regions, .htif_tohost_base, .hart_state, .mcountinhibit, .minstretcfg]

def Stable (initial after : RegisterFile) : Prop :=
  ∀ r ∈ stableControls, after r = initial r

structure Result (initial : RegisterFile) (original : HartTp.GprFile) (cpu : CPU)
    (after : RegisterFile) (values : HartTp.GprFile) : Prop where
  config : Config after
  stable : Stable initial after
  pc : after .PC = MycpuReturn.retPC (HartTp.rget cpu original 1#5)
  nextPC : after .nextPC = MycpuReturn.retPC (HartTp.rget cpu original 1#5)
  mapOther : ∀ key, key ≠ 10#5 → key ≠ 15#5 → values key = original key
  sp : HartTp.rget cpu values 2#5 = entrySP cpu original
  ra : HartTp.rget cpu values 1#5 = HartTp.rget cpu original 1#5
  s0 : HartTp.rget cpu values 8#5 = HartTp.rget cpu original 8#5
  calleeSaved : CalleeSaved.Preserved (entry initial cpu original) (entry after cpu values)
  value : HartTp.rget cpu values 10#5 = MycpuScalar.mycpuRet (HartTp.hartWord cpu)
  cpuAddress : (HartTp.rget cpu values 10#5).toNat = 0x800123e8 + 128 * cpu.val

/-- A receipt record retains its actual instruction index and dependent body
outcome, so the final list does not discard successful fetch/A-D/data views. -/
structure Receipt where
  index : Fin 14
  fetchTrace : List KptFetchHalf.Step
  outcome : MycpuKptCycle.Outcome index

def Ordered (trace : List Receipt) : Prop := trace.map (fun r => r.index.val) = List.range 14

variable {GF : BundledGFunctors} (capacity : Capacity GF)

noncomputable def receipts (era : Era.Record) (cpu : CPU) (sp : BitVec 64) : List Receipt → IProp GF
  | [] => iprop(emp)
  | r :: rest => iprop(MycpuKptCycle.receipts capacity era cpu r.index sp r.fetchTrace r.outcome ∗
      receipts era cpu sp rest)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def resources (era : Era.Record) (cpu : CPU) (shares : Shares)
    (control : RegisterFile) (values : HartTp.GprFile) (N : Namespace) (root : PtTree.PPN)
    (tier : KernelDatum.Tier) (ξ : TsoContext.CtxId) (sp : BitVec 64) (words : Words)
    (rr : Option Reservation) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) control values shares ∗ code capacity era tier ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗ pair capacity era tier ξ sp words ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗ frame)

/-- The only continuation WP is the real cycle after return. All fourteen
instruction guards are discharged internally, preserving their receipts. -/
noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (shares : Shares) (initial : RegisterFile) (original : HartTp.GprFile)
    (N : Namespace) (root : PtTree.PPN) (tier : KernelDatum.Tier) (ξ : TsoContext.CtxId)
    (frame : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ after values trace, ⌜Result initial original cpu after values ∧ Ordered trace⌝ -∗
    resources capacity era cpu shares after values N root tier ξ (entrySP cpu original)
      (savedWords cpu original) none frame -∗
    receipts capacity era cpu (entrySP cpu original) trace -∗
    ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)

end Xv6.Kernel.MycpuKpt
