import Xv6.Kernel.PushOffWord4Defs
namespace Xv6.Kernel.PushOffWord4
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec [Platform] : Prop where
  factor : ∀ op, body op = factored op
  normalized : ∀ op, PushOffCode.normalized (index op) =
    match kind op with
    | .load => .LOAD (immediate op, .Regidx 10#5, .Regidx 15#5, false, 4)
    | .store => .STORE (immediate op, .Regidx 15#5, .Regidx 10#5, 4)
  compressed : ∀ op, execute (PushOffCode.decoded (index op)) =
    pure (.ExecuteAs (PushOffCode.normalized (index op)))
  storeFalse : storeTail (.Ok false) = pure (.Retire_Success ())
  storeError : ∀ error, storeTail (.Err error) = pure error
  loadError : ∀ error, loadTail (.Err error) = pure error
  footprintUnique : ∀ shares, RegisterFootprint.Unique (footprint shares)
  footprintCounts : ∀ shares, (footprint shares).length = 7 ∧
    (remainderFootprint shares).length = 43 ∧ (bareFootprint shares).length = 10
  footprintMembers : ∀ shares cell, cell ∈ footprint shares → cell ∈ MycpuRegimeShell.footprint shares
  kptAmbient : ∀ control cpu values N root, Config (.kpt N root) control →
    SupervisorBits.MsFacts (control .mstatus) → KptMemory4.Ambient (entry control cpu values)
  bareConfig : ∀ control cpu values satp pmp, Config .bare control →
    SupervisorBits.MsFacts (control .mstatus) → _get_Satp64_Mode (Mk_Satp64 satp) = 0#4 →
    MachCSL.Machine.SupervisorPmp.TorRam pmp →
    PushOffWord4Bare.Config (entry (MycpuBareSource.patch control satp pmp) cpu values)
  mapOther : ∀ op values old i, i ≠ 15#5 → afterMap op values old i = values i
  afterAddress : ∀ op cpu values old other,
    address cpu (afterMap op values old) other = address cpu values other
  afterSP : ∀ op cpu values old,
    HartTp.rget cpu (afterMap op values old) 2#5 = HartTp.rget cpu values 2#5

structure ResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  packetKpt : ∀ era cpu control values shares N root,
    iprop(packet capacity era cpu (.kpt N root) control values shares ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry control cpu values) (footprint shares) ∗
      KptResidue.residue capacity.translation era cpu N root ∗
      packetFrame capacity era cpu control values shares)
  packetBare : ∀ era cpu control values shares,
    iprop(packet capacity era cpu .bare control values shares ⊣⊢
      barePacket capacity era cpu control values shares)
  identityWord : ∀ era ξ va dq old,
    iprop(KernelDatumWord4.word capacity.translation era .identity ξ va dq old ⊢
      ⌜KernelDatumWord4.Aligned va ∧ SupervisorPhysical.RamRange va 4⌝ ∗
      TsoContextBytesReadWP.window capacity.machine era ξ va 4 dq old ∗
      (∀ newValue, TsoContextBytesReadWP.window capacity.machine era ξ va 4 dq newValue -∗
        KernelDatumWord4.word capacity.translation era .identity ξ va dq newValue))

/-- Both actual normalized instruction arms discharge transform, translation,
physical memory and destination writes internally. The supplied word stays at
its original tier; only the source Bare/identity compatibility is required. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  body : ∀ regime shares control values, Config regime control →
    ∀ op tier ξ dq old rr, MycpuRegimeShell.Admits regime tier →
    (kind op = .store → dq = .own 1) →
    ∀ image fixed whole gen era cpu (frame : IProp GF) continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatumWord4.word capacity.translation era tier ξ (address cpu values op) dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu regime control values shares op tier ξ dq old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (PushOffWord4.body op >>= continuation)) post)
end Xv6.Kernel.PushOffWord4
