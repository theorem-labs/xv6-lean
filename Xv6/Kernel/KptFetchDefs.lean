import Xv6.Kernel.KptFetchHalfDefs

/-! Source InstrBytes and actual shared-Sv39 fetch. A two-aligned base
instruction can use two independently mapped pages. No body-WP input. -/
namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptFetchHalf.Capacity
abbrev Tier := KernelTextDatum.Tier

structure Shares where
  pc : DFrac
  misa : DFrac
  translation : KptFetchHalf.Shares

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.PC, shares.pc), (.misa, shares.misa)] ++ KptFetchHalf.footprint shares.translation

structure Config (rs : RegisterFile) : Prop where
  translation : KptFetchHalf.Config rs
  compressed : _get_Misa_C (rs .misa) = 1#1

def program : SailM FetchResult := fetch ()

/-- The complete generated branch tree with only its fetch-chunk calls
abstracted. Alignment, extension and translation/read error paths are retained. -/
def factor (fetchChunk : (start address : BitVec 64) → (n : Nat) → SailM (FetchBytes_Result n)) : SailM FetchResult := _root_.Sail.SailME.run do
  if ((get_config_rvfi ()) : Bool)
  then (rvfi_fetch ())
  else
    (do
      match (ext_fetch_check_pc (← _root_.Sail.readReg .PC) (← _root_.Sail.readReg .PC)) with
      | .some e => _root_.Sail.SailME.throw ((.F_Ext_Error e) : FetchResult)
      | none => (pure ())
      if ((((Sail.BitVec.access (← _root_.Sail.readReg .PC) 0) != 0#1) || (((Sail.BitVec.access (← _root_.Sail.readReg .PC) 1) != 0#1) && (LeanPaperStock.Functions.not
               (← (currentlyEnabled .Ext_Zca))))) : Bool)
      then (pure (.F_Error ((.E_Fetch_Addr_Align ()), (← _root_.Sail.readReg .PC))))
      else
        (do
          if (((is_aligned_vaddr (.Virtaddr (← _root_.Sail.readReg .PC)) 4) && (← (currentlyEnabled .Ext_Ziccif))) : Bool)
          then
            (do
              match (← (fetchChunk (← _root_.Sail.readReg .PC) (← _root_.Sail.readReg .PC) 4)) with
              | .FetchBytes_Ext_Error e => (pure (.F_Ext_Error e))
              | .FetchBytes_Exception e => (pure (.F_Error (e, (← _root_.Sail.readReg .PC))))
              | .FetchBytes_Success bytes =>
                (if ((isRVC (Sail.BitVec.extractLsb bytes 15 0)) : Bool)
                then (pure (.F_RVC (Sail.BitVec.extractLsb bytes 15 0)))
                else (pure (.F_Base bytes))))
          else
            (do
              match (← (fetchChunk (← _root_.Sail.readReg .PC) (← _root_.Sail.readReg .PC) 2)) with
              | .FetchBytes_Ext_Error e => (pure (.F_Ext_Error e))
              | .FetchBytes_Exception e => (pure (.F_Error (e, (← _root_.Sail.readReg .PC))))
              | .FetchBytes_Success ilo =>
                (do
                  if ((isRVC ilo) : Bool)
                  then (pure (.F_RVC ilo))
                  else
                    (do
                      match (← (fetchChunk (← _root_.Sail.readReg .PC) (Sail.BitVec.addInt (← _root_.Sail.readReg .PC) 2) 2)) with
                      | .FetchBytes_Ext_Error e => (pure (.F_Ext_Error e))
                      | .FetchBytes_Exception e =>
                        (pure (.F_Error (e, (Sail.BitVec.addInt (← _root_.Sail.readReg .PC) 2))))
                      | .FetchBytes_Success ihi => (pure (.F_Base (ihi +++ ilo))))))))

/-- Exact chunk addresses, not physical addresses. The RVC aligned-four
case still has a four-byte window even though its result is only sixteen bits. -/
def chunks (pc : BitVec 64) : FetchResult → List (BitVec 64)
  | .F_Base _ => if is_aligned_vaddr (.Virtaddr pc) 4 then [pc] else [pc, addressAdd pc 2]
  | .F_RVC _ => [pc]
  | _ => []

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Exact source InstrBytes, including false fetch-error branches and the
existential extra bytes required by a four-aligned compressed instruction. -/
def instrBytes (era : Era.Record) (tier : Tier) (pc : BitVec 64) (result : FetchResult) : IProp GF :=
  let body : IProp GF := match result with
    | .F_Base word => iprop(⌜isRVC (KernelTextDatum.lowHalf word) = false⌝ ∗
        KernelTextDatum.window capacity era tier pc 4 .discard word)
    | .F_RVC half => iprop(⌜isRVC half = true⌝ ∗
        if is_aligned_vaddr (.Virtaddr pc) 4 then
          ∃ word : BitVec 32, ⌜KernelTextDatum.lowHalf word = half⌝ ∗
            KernelTextDatum.window capacity era tier pc 4 .discard word
        else KernelTextDatum.window capacity era tier pc 2 .discard half)
    | _ => iprop(False)
  iprop(⌜is_aligned_vaddr (.Virtaddr pc) 2 = true⌝ ∗ body)

abbrev cells (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (footprint shares)

/-- Event guards in actual execution order. This is a finite modal fold,
not an assumed fetch WP, trace feasibility fact or successful translator. -/
def guardChunks (rs : RegisterFile) (root : PtTree.PPN) (addresses : List (BitVec 64))
    (done : List KptFetchHalf.Step → IProp GF) : IProp GF :=
  addresses.foldr (fun address next trace =>
    KptFetchHalf.guard rs root address (fun step => next (trace ++ [step]))) done []

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def resources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (rr : Option Reservation) (trace : List KptFetchHalf.Step)
    (tier : Tier) (result : FetchResult) : IProp GF :=
  iprop(cells capacity era cpu rs shares ∗ KptResidue.residue capacity era cpu N root ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (KptFetchHalf.traceReservation rr trace) ∗ KptFetchHalf.receipts capacity era cpu trace ∗
    instrBytes capacity era tier (rs .PC) result)

noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (tier : Tier) (result : FetchResult) (rr : Option Reservation)
    (continuation : FetchResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  guardChunks rs root (chunks (rs .PC) result) (fun trace => iprop(
    resources capacity era cpu rs shares N root rr trace tier result -∗
    MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation result)) post))

end Xv6.Kernel.KptFetch
