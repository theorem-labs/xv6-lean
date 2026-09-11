import Xv6.Kernel.KptFetchSpec

/-! Proof-side finite execution plans. Each chunk node is discharged by the
native KptFetchHalf theorem; no caller supplies a plan or a chunk body WP. -/
namespace Xv6.Kernel.KptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure Chunk where
  start : BitVec 64
  address : BitVec 64
  width : Nat
  word : BitVec (8 * width)

def classified (word : BitVec 32) : FetchResult :=
  if isRVC (KernelTextDatum.lowHalf word) then .F_RVC (KernelTextDatum.lowHalf word) else .F_Base word

def parts (pc : BitVec 64) (word : BitVec 32) : List Chunk :=
  if is_aligned_vaddr (.Virtaddr pc) 4 then [⟨pc,pc,4,word⟩]
  else if isRVC (KernelTextDatum.lowHalf word) then [⟨pc,pc,2,KernelTextDatum.lowHalf word⟩]
  else [⟨pc,pc,2,KernelTextDatum.lowHalf word⟩,
    ⟨pc,addressAdd pc 2,2,KernelTextDatum.highHalf word⟩]

inductive Plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) :
    List Chunk → SailM α → α → Prop where
  | pure (value : α) : Plan fp rs [] (pure value) value
  | prefix {β : Type} {segment : SailM β} {value : β} {next : β → SailM α} {result : α} {chunks}
      (before : RegisterPlan.Returns fp rs segment value rs)
      (rest : Plan fp rs chunks (next value) result) : Plan fp rs chunks (segment >>= next) result
  | chunk (part : Chunk) {next : FetchBytes_Result part.width → SailM α} {result : α} {chunks}
      (width : KptFetchHalf.Supported part.width)
      (aligned : is_aligned_vaddr (.Virtaddr part.address) part.width = true)
      (rest : Plan fp rs chunks (next (.FetchBytes_Success part.word)) result) :
      Plan fp rs (part :: chunks) (KptFetchHalf.program part.start part.address part.width >>= next) result

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def chunkWindows (era : Era.Record) (tier : Tier) (parts : List Chunk) : IProp GF :=
  iprop([∗list] part ∈ parts, KernelTextDatum.window capacity era tier part.address part.width .discard part.word)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def runResources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares)
    (N : Namespace) (root : PtTree.PPN) (rr : Option Reservation) (trace : List KptFetchHalf.Step) : IProp GF :=
  iprop(cells capacity era cpu rs shares ∗ KptResidue.residue capacity era cpu N root ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (KptFetchHalf.traceReservation rr trace) ∗ KptFetchHalf.receipts capacity era cpu trace)

end Xv6.Kernel.KptFetch
