import Xv6.Kernel.BareJalFetchDefs
import Xv6.Kernel.KptJalDefs
import Xv6.Kernel.MycpuBareSourceDefs

/-! Actual JAL x1 on the source fifty-cell Bare packet. The three Bare
translation cells are existentially owned, not read from an arbitrary file. -/
namespace Xv6.Kernel.BareJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev Config := KptJal.Config
abbrev entry := MycpuRegimeShell.entry
abbrev started := MycpuRegimeShell.started
abbrev instruction := KptJal.instruction
abbrev encoding := KptJal.encoding
abbrev result := KptJal.result
abbrev target := KptJal.target
abbrev TargetEven := KptJal.TargetEven
abbrev prepared := KptJal.prepared
abbrev afterControl := KptJal.afterControl
abbrev afterValues := KptJal.afterValues
abbrev body [Platform] (imm : BitVec 21) := KptJal.body imm
abbrev executeTail [Platform] (imm : BitVec 21) := KptJal.executeTail imm
abbrev patch := MycpuBareSource.patch
abbrev shares := MycpuRegimeShell.sourceShares

def fetchShares : BareJalFetch.Shares :=
  ⟨.own 1,.discard,⟨⟨.own 1,.own 1,.own 1⟩,⟨.discard,.own 1,.own 1,.discard⟩⟩⟩

def fullFootprint : RegisterFootprint.Footprint :=
  MycpuRegimeShell.footprint shares ++ [(.satp,.own 1),(.pmpcfg_n,.own 1),(.pmpaddr_n,.own 1)]

def restFootprint : RegisterFootprint.Footprint :=
  fullFootprint.filter (fun cell => !((BareJalFetch.footprint fetchShares).map Prod.fst).contains cell.1)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def fetchFrame (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : File) : IProp GF :=
  iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry control cpu values) restFootprint ∗
    MycpuRegimeShell.bitFrame capacity era cpu (control .mstatus) ∗ ⌜values 0#5 = 0#64⌝)

def code (era : Era.Record) (pc : BitVec 64) (imm : BitVec 21) : IProp GF :=
  KptJal.code capacity era .identity pc imm

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def packet (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : File) : IProp GF :=
  MycpuRegimeShell.resources capacity era cpu .bare control values shares

noncomputable def fetchResources (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (control : RegisterFile) (values : File) (pc : BitVec 64) (imm : BitVec 21)
    (rr : Option Reservation) (views : List Nat) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu control values ∗ code capacity era pc imm ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗
    BareJalFetch.receipts capacity.translation era cpu views ∗ frame)

noncomputable def bodyResources (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (control : RegisterFile) (values : File) (pc : BitVec 64) (imm : BitVec 21) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (afterControl pc imm control) (afterValues pc values) ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗ frame)

noncomputable def activeResources (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (control : RegisterFile) (values : File) (pc : BitVec 64) (imm : BitVec 21)
    (rr : Option Reservation) (views : List Nat) (frame : IProp GF) : IProp GF :=
  fetchResources capacity era cpu ξ (afterControl pc imm control) (afterValues pc values) pc imm rr views frame

noncomputable def cycleResources (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (after : RegisterFile) (values : File) (pc : BitVec 64) (imm : BitVec 21)
    (views : List Nat) (frame : IProp GF) : IProp GF :=
  fetchResources capacity era cpu ξ after (afterValues pc values) pc imm none views frame

noncomputable def fetchFinish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (control : RegisterFile) (values : File) (pc : BitVec 64) (imm : BitVec 21) (rr : Option Reservation)
    (frame : IProp GF) (continuation : FetchResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  BareJalFetch.guards pc (fun views => iprop(fetchResources capacity era cpu ξ control values pc imm rr views frame -∗
    RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (result imm))) post))

noncomputable def activeFinish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (control : RegisterFile) (values : File) (pc : BitVec 64) (imm : BitVec 21) (rr : Option Reservation)
    (frame : IProp GF) (continuation : Step → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  BareJalFetch.guards pc (fun views => iprop(activeResources capacity era cpu ξ control values pc imm rr views frame -∗
    RegisterWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (continuation (.Step_Execute (.Retire_Success (),encoding imm)))) post))

noncomputable def cycleFinish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (control : RegisterFile) (values : File) (pc : BitVec 64) (imm : BitVec 21)
    (frame : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  BareJalFetch.guards pc (fun views => iprop(∀ after,
    ⌜MycpuRegimeShell.Completed (afterControl pc imm (started control)) after⌝ -∗
    ▷ ∀ nextTick, cycleResources capacity era cpu ξ after values pc imm views frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post))

end Xv6.Kernel.BareJal
