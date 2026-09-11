import Xv6.Kernel.BareFetchDefs
import Xv6.Kernel.BareJalDefs

/-! Same-source-share instruction fetch over the actual disabled translation
regime. The input code is at its original admitted tier. -/
namespace Xv6.Kernel.RegimeFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev Regime := MycpuRegimeShell.Regime
abbrev Tier := KernelTextDatum.Tier
abbrev Config := KptJal.Config
abbrev entry := MycpuRegimeShell.entry
abbrev shares := MycpuRegimeShell.sourceShares
abbrev program := KptFetch.program

def Trace : Regime → Type
  | .bare => List Nat
  | .kpt _ _ => List KptFetchHalf.Step

def afterReservation (regime : Regime) (rr : Option Reservation) : Trace regime → Option Reservation :=
  match regime with
  | .bare => fun _ => rr
  | .kpt _ _ => KptFetchHalf.traceReservation rr

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def code (era : Era.Record) (tier : Tier) (pc : BitVec 64) (result : FetchResult) : IProp GF :=
  KptFetch.instrBytes capacity.translation era tier pc result

def receipts (era : Era.Record) (cpu : CPU) (regime : Regime) : Trace regime → IProp GF :=
  match regime with
  | .bare => BareFetch.receipts capacity.translation era cpu
  | .kpt _ _ => KptFetchHalf.receipts capacity.translation era cpu

def guards (regime : Regime) (control : RegisterFile) (cpu : CPU) (values : File)
    (result : FetchResult) (next : Trace regime → IProp GF) : IProp GF :=
  match regime with
  | .bare => BareFetch.guards (control .PC) result next
  | .kpt _ root => KptFetch.guardChunks (entry control cpu values) root
      (KptFetch.chunks (control .PC) result) next

variable {hlc : HasLC} [InvGS_gen hlc GF]
noncomputable def packet (era : Era.Record) (cpu : CPU) (regime : Regime)
    (control : RegisterFile) (values : File) : IProp GF :=
  MycpuRegimeShell.resources capacity era cpu regime control values shares

noncomputable def resources (era : Era.Record) (cpu : CPU) (regime : Regime)
    (control : RegisterFile) (values : File) (tier : Tier) (result : FetchResult)
    (ξ : TsoContext.CtxId) (rr : Option Reservation) (trace : Trace regime) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu regime control values ∗ code capacity era tier (control .PC) result ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (afterReservation regime rr trace) ∗ receipts capacity era cpu regime trace ∗ frame)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (regime : Regime)
    (control : RegisterFile) (values : File) (tier : Tier) (result : FetchResult)
    (ξ : TsoContext.CtxId) (rr : Option Reservation) (frame : IProp GF)
    (continuation : FetchResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  guards regime control cpu values result (fun trace => iprop(
    resources capacity era cpu regime control values tier result ξ rr trace frame -∗
    RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation result)) post))
end Xv6.Kernel.RegimeFetch
