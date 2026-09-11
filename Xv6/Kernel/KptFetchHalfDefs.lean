import Xv6.Kernel.KptAddressDefs
import Xv6.Kernel.KernelTextDatumDefs
import MachCSL.Logic.SupervisorFetchReadDefs

/-! Actual supervisor fetch chunk, with native text and shared KPT resources.
Translation errors remain in the raw factor; the successful RX route must be
proved using owned ADUE and the text mapping, not supplied as a WP premise. -/
namespace Xv6.Kernel.KptFetchHalf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptAddress.Capacity
abbrev Shares := KptAddress.Shares
abbrev Tier := KernelTextDatum.Tier
abbrev Supported := SupervisorFetchRead.Supported
abbrev footprint := KptAddress.auxiliaryFootprint

structure Config (rs : RegisterFile) : Prop where
  ambient : KptAddress.Ambient rs
  adue : _get_MEnvcfg_ADUE (rs .menvcfg) = 1#1

def program (start address : BitVec 64) (n : Nat) : SailM (FetchBytes_Result n) :=
  fetch_bytes start address n

/-- Preserve the generated assertion and error address for every raw result. -/
def afterTranslation (n : Nat) : KptAddress.Result → SailM (FetchBytes_Result n)
  | .Err (e, _) => pure (.FetchBytes_Exception e)
  | .Ok (pa, pbmt, _) => do
      match ← mem_read (.InstructionFetch ()) pbmt pa n false false false with
      | .Err (exc_addr,e) => do
          _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.assert (exc_addr == pa) "postlude/fetch.sail:44.30-44.31"
          pure (.FetchBytes_Exception e)
      | .Ok bytes => pure (.FetchBytes_Success bytes)

/-- Actual source translation witnesses, followed by the physical read view.
The original residue values are recorded separately for every call. -/
structure Step where
  address : BitVec 64
  ppn : PtTree.PPN
  data : KptAddress.Data
  tree : PtTree.Tree
  p2 : PtTree.Word
  p1 : PtTree.Word
  referenceA : Bool
  referenceD : Bool
  branch : KptTranslate.Branch
  readView : Nat

def Step.outcome (step : Step) : KptAddress.Outcome :=
  .translated step.tree step.p2 step.p1 step.referenceA step.referenceD step.branch

def Step.afterReservation (rr : Option Reservation) (step : Step) : Option Reservation :=
  KptAddress.afterReservation step.address rr step.outcome

def Step.Facts (rs : RegisterFile) (root : PtTree.PPN) (step : Step) : Prop :=
  KptAddress.OutcomeFacts rs step.data root step.address step.ppn .rx (.InstructionFetch ()) step.outcome

def traceReservation (rr : Option Reservation) (trace : List Step) : Option Reservation :=
  trace.foldl (fun current step => step.afterReservation current) rr

variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev cells := KptAddress.auxiliaryCells capacity
abbrev window := KernelTextDatum.window capacity

def receipt (era : Era.Record) (cpu : CPU) (step : Step) : IProp GF :=
  iprop(KptAddress.receipts capacity era cpu step.address step.outcome ∗
    Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) step.readView)

def receipts (era : Era.Record) (cpu : CPU) (trace : List Step) : IProp GF :=
  iprop([∗list] step ∈ trace, receipt capacity era cpu step)

/-- No body WP appears here. A miss supplies three walk guards; A/D adds
zero/one/two, and the actual plain instruction read adds exactly one. All
unknown observed-word facts remain inside their A/D event guards. -/
def guard (rs : RegisterFile) (root : PtTree.PPN) (address : BitVec 64)
    (next : Step → IProp GF) : IProp GF :=
  iprop(∀ ppn data tree p2 p1 referenceA referenceD,
    ⌜Sv39Address.Canonical address ∧ KptAddress.Path rs data root address ppn .rx tree p2 p1 referenceA referenceD⌝ -∗
    ((∀ a d update, KptAD.guarded update iprop(
      ⌜KptAddress.OutcomeFacts rs data root address ppn .rx (.InstructionFetch ())
        (.translated tree p2 p1 referenceA referenceD (.hit a d update))⌝ -∗
      ▷ (∀ view, next ⟨address,ppn,data,tree,p2,p1,referenceA,referenceD,.hit a d update,view⟩))) ∧
     ▷ ▷ ▷ (∀ a d view2 view1 view0 update, KptAD.guarded update iprop(
      ⌜KptAddress.OutcomeFacts rs data root address ppn .rx (.InstructionFetch ())
        (.translated tree p2 p1 referenceA referenceD (.miss a d view2 view1 view0 update))⌝ -∗
      ▷ (∀ view, next ⟨address,ppn,data,tree,p2,p1,referenceA,referenceD,.miss a d view2 view1 view0 update,view⟩)))))

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def resources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (rr : Option Reservation) (trace : List Step) : IProp GF :=
  iprop(cells capacity era cpu rs shares ∗ KptResidue.residue capacity era cpu N root ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu (traceReservation rr trace) ∗
    receipts capacity era cpu trace)

noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (tier : Tier) (address : BitVec 64) (n : Nat) (word : BitVec (8*n))
    (rr : Option Reservation) (continuation : FetchBytes_Result n → SailM Unit)
    (post : Empty → IProp GF) : IProp GF :=
  guard rs root address (fun step => iprop(
    resources capacity era cpu rs shares N root rr [step] -∗
    window capacity era tier address n .discard word -∗
    MemoryReadWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (continuation (.FetchBytes_Success word))) post))

end Xv6.Kernel.KptFetchHalf
