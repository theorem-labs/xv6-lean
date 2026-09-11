import Xv6.Kernel.KptMemory4Defs
import MachCSL.Logic.SupervisorBareFetchDefs

/-! Internal size-four Bare virtual-memory prerequisite. The public instruction
rule derives physical geometry from the original identity-tier word. -/
namespace Xv6.Kernel.PushOffWord4Bare
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
abbrev Kind := KptMemory4.Kind
abbrev Result := KptMemory4.Result
abbrev program [Platform] := KptMemory4.program
abbrev addressProgram [Platform] := KptMemory4.addressProgram

structure Shares where
  bare : SupervisorBareFetch.Shares
  environment : DFrac

def footprint (s : Shares) : RegisterFootprint.Footprint :=
  [(.menvcfg, s.environment)] ++ SupervisorBareFetch.footprint s.bare

def transformShares (s : Shares) : SupervisorAddress.Shares :=
  ⟨s.bare.translation.status, s.bare.translation.privilege, s.environment, s.bare.translation.satp⟩

structure Config (rs : RegisterFile) : Prop where
  transform : SupervisorAddress.Config rs .Bare
  tor : MachCSL.Machine.SupervisorPmp.TorRam rs
  pma : rs .pma_regions = pmaBoot
  htif : rs .htif_tohost_base = none

def afterReservation : Kind → Option Reservation → Option Reservation
  | .load, rr => rr
  | .store, _ => none

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
abbrev cells (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (s : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint s)

def resources (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (s : Shares)
    (kind : Kind) (ξ : TsoContext.CtxId) (va : BitVec 64) (dq : DFrac)
    (old new : BitVec 32) (rr : Option Reservation) (view : Nat) : IProp GF :=
  iprop(cells capacity era cpu rs s ∗ TsoContextReadWP.running capacity era cpu ξ ∗
    TsoContextBytesReadWP.window capacity era ξ va 4 dq (KptMemory4.valueAfter kind old new) ∗
    Reservations.resvFrag capacity.era.reservations era.reservations cpu (afterReservation kind rr) ∗
    Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view)

variable {hlc : HasLC} [InvGS_gen hlc GF]
noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU)
    (rs : RegisterFile) (s : Shares) (kind : Kind) (ξ : TsoContext.CtxId)
    (va : BitVec 64) (dq : DFrac) (old new : BitVec 32) (rr : Option Reservation)
    (continuation : Result kind → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  iprop(▷ ∀ view, resources capacity era cpu rs s kind ξ va dq old new rr view -∗
    RegisterWP.threadWP capacity image fixed whole
      (.hart gen cpu (continuation (KptMemory4.result kind old))) post)
end Xv6.Kernel.PushOffWord4Bare
