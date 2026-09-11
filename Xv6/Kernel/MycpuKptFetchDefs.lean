import Xv6.Kernel.MycpuRegimeShellDefs
import Xv6.Kernel.KptFetchDefs
import Xv6.Kernel.MycpuFetchDefs

/-! Actual indexed mycpu instruction fetch over the source fifty-cell packet.
The code input is fourteen virtual RX/pristine windows, including the two
following bytes that the generated final aligned fetch actually reads. -/
namespace Xv6.Kernel.MycpuKptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev Tier := KernelTextDatum.Tier
abbrev entry := MycpuRegimeShell.entry
noncomputable abbrev packet := @MycpuRegimeShell.resources
abbrev result := MycpuFetch.result
abbrev program := KptFetch.program

/-- PC and mstatus are full in the source packet; the other shares are
borrowed unchanged. SATP/TLB/PMP vectors remain solely inside the residue. -/
def fetchShares (shares : Shares) : KptFetch.Shares :=
  ⟨.own 1, shares.misa, ⟨.own 1, shares.privilege, shares.pma, shares.htif, shares.environment⟩⟩
def footprint (shares : Shares) : RegisterFootprint.Footprint := KptFetch.footprint (fetchShares shares)
def remainderFootprint (shares : Shares) : RegisterFootprint.Footprint :=
  (MycpuRegimeShell.footprint shares).filter
    (fun cell => !((footprint shares).map Prod.fst).contains cell.1)

/-- Hardware facts outside msOwn. Its source MsFacts supplies SXL=2;
no translation success or physical address/word is given by this Config. -/
structure Config (control : RegisterFile) : Prop where
  privilege : control .cur_privilege = .Supervisor
  pma : control .pma_regions = pmaBoot
  htif : control .htif_tohost_base = none
  compressed : _get_Misa_C (control .misa) = 1#1
  adue : _get_MEnvcfg_ADUE (control .menvcfg) = 1#1

/-- Exact source InstrBytes.v decoder, including its unused error default.
This only identifies the eventual decoder program; the fetch WP does not
execute it or assume its successful WP. -/
def decodeFetch : FetchResult → SailM instruction
  | .F_Base word => ext_decode word
  | .F_RVC half => ext_decode_compressed half
  | _ => ext_decode 0#32

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Virtual text ownership; full tier may have nonidentity physical pages. -/
def window (era : Era.Record) (tier : Tier) (i : Fin 14) : IProp GF :=
  KernelTextDatum.window capacity.translation era tier (MycpuDecode.address i)
    (MycpuFetchBytes.width i) .discard (MycpuFetchBytes.word i)

/-- The fourteen windows cover the actual 34-byte fetch footprint. Overlapping
bytes use the source discard share; no code ownership is allocated here. -/
def code (era : Era.Record) (tier : Tier) : IProp GF :=
  iprop([∗list] i ∈ List.finRange 14, window capacity era tier i)

def packetFrame (era : Era.Record) (cpu : CPU) (control : RegisterFile)
    (values : HartTp.GprFile) (shares : Shares) : IProp GF :=
  iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry control cpu values) (remainderFootprint shares) ∗
    MycpuRegimeShell.bitFrame capacity era cpu (control .mstatus) ∗ ⌜values 0#5 = 0#64⌝)

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Complete restored packet, updated coherent KPT residue, exact reservation
and every actual translation/read receipt, with original code and frame. -/
noncomputable def resources (era : Era.Record) (cpu : CPU) (control : RegisterFile)
    (values : HartTp.GprFile) (shares : Shares) (N : Namespace) (root : PtTree.PPN)
    (tier : Tier) (rr : Option Reservation) (trace : List KptFetchHalf.Step)
    (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) control values shares ∗
    code capacity era tier ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (KptFetchHalf.traceReservation rr trace) ∗
    KptFetchHalf.receipts capacity.translation era cpu trace ∗ frame)

/-- Exactly the shared fetch's hit/miss/A-D/plain-read guards. Unknown
observations retain their original scope; no fixed TLB snapshot is reused. -/
noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (control : RegisterFile)
    (values : HartTp.GprFile) (shares : Shares) (N : Namespace) (root : PtTree.PPN)
    (tier : Tier) (i : Fin 14) (rr : Option Reservation) (frame : IProp GF)
    (continuation : FetchResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  KptFetch.guardChunks (entry control cpu values) root
    (KptFetch.chunks (MycpuDecode.address i) (result i)) (fun trace => iprop(
      resources capacity era cpu control values shares N root tier rr trace frame -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (result i))) post))

end Xv6.Kernel.MycpuKptFetch
