import Xv6.Kernel.BareJalFetchDefs

/-! General actual Bare fetch, including compressed instructions. Reuses the
native generic chunk/outer-plan machinery; only the public result boundary
extends the earlier JAL-only wrapper. -/
namespace Xv6.Kernel.BareFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
abbrev Capacity := BareJalFetch.Capacity
abbrev Shares := BareJalFetch.Shares
abbrev Config := BareJalFetch.Config
abbrev footprint := BareJalFetch.footprint
abbrev cells := @BareJalFetch.cells
abbrev program := BareJalFetch.program
abbrev guardReads := @BareJalFetch.guardReads
abbrev receipts := @BareJalFetch.receipts

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def code (era : Era.Record) (pc : BitVec 64) (result : FetchResult) : IProp GF :=
  KptFetch.instrBytes capacity era .identity pc result

def guards (pc : BitVec 64) (result : FetchResult) (done : List Nat → IProp GF) : IProp GF :=
  guardReads (KptFetch.chunks pc result) done

def resources (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (rs : RegisterFile) (shares : Shares) (result : FetchResult) (views : List Nat) : IProp GF :=
  iprop(cells capacity era cpu rs shares ∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ ∗
    code capacity era (rs .PC) result ∗ receipts capacity era cpu views)

variable {hlc : HasLC} [InvGS_gen hlc GF]
noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (rs : RegisterFile) (shares : Shares) (result : FetchResult)
    (continuation : FetchResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  guards (rs .PC) result (fun views => iprop(resources capacity era cpu ξ rs shares result views -∗
    RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation result)) post))
end Xv6.Kernel.BareFetch
