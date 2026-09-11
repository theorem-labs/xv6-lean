import Xv6.Kernel.KptFetchPlanDefs
import Xv6.Kernel.MycpuFetchDefs

/-! Generic base-instruction fetch in the actual Bare translation lane.
The outer generated fetch plan is shared with KptFetch; the native chunk
implementation uses the owned Bare SATP/PMP cells and identity text. -/
namespace Xv6.Kernel.BareJalFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KernelTextDatum.Capacity
abbrev Shares := MycpuFetch.Shares

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.PC,shares.pc),(.misa,shares.misa)] ++ SupervisorBareFetch.footprint shares.bare

structure Config (rs : RegisterFile) : Prop where
  bare : SupervisorBare.Config rs
  tor : SupervisorPmp.TorRam rs
  pma : rs .pma_regions = pmaBoot
  htif : rs .htif_tohost_base = none
  compressed : _get_Misa_C (rs .misa) = 1#1

abbrev program := KptFetch.program
abbrev Chunk := KptFetch.Chunk
abbrev Plan := KptFetch.Plan
abbrev parts := KptFetch.parts
abbrev classified := KptFetch.classified

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def cells (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (footprint shares)

/-- Source identity-tier InstrBytes: actual four-byte RX/pristine virtual
ownership, two-alignment and non-RVC classification, not a successful WP. -/
def code (era : Era.Record) (pc : BitVec 64) (word : BitVec 32) : IProp GF :=
  KptFetch.instrBytes capacity era .identity pc (.F_Base word)

/-- Each actual ordinary instruction read contributes precisely one later
and its returned view. The address fold retains read order at a split fetch. -/
def guardReads (addresses : List (BitVec 64)) (done : List Nat → IProp GF) : IProp GF :=
  addresses.foldr (fun _ next views => iprop(▷ ∀ view : Nat, next (views ++ [view]))) done []

def guards (pc : BitVec 64) (done : List Nat → IProp GF) : IProp GF :=
  guardReads (KptFetch.chunks pc (.F_Base 0#32)) done

def receipts (era : Era.Record) (cpu : CPU) (views : List Nat) : IProp GF :=
  iprop([∗list] view ∈ views, Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view)

def resources (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (rs : RegisterFile) (shares : Shares) (word : BitVec 32) (views : List Nat) : IProp GF :=
  iprop(cells capacity era cpu rs shares ∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ ∗
    code capacity era (rs .PC) word ∗ receipts capacity era cpu views)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (rs : RegisterFile) (shares : Shares) (word : BitVec 32)
    (continuation : FetchResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  guards (rs .PC) (fun views => iprop(resources capacity era cpu ξ rs shares word views -∗
    RegisterWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (continuation (.F_Base word))) post))

end Xv6.Kernel.BareJalFetch
