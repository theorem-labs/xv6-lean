import Xv6.Kernel.BareJalDefs

/-! The actual opened identity/Bare source arm. JAL uses no stack slots;
all stack, timer, pending/stvec, hardware and caller resources are retained. -/
namespace Xv6.Kernel.BareJalSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := BareJal.Capacity
abbrev File := HartTp.GprFile
abbrev afterFile := KptJal.afterValues
abbrev bootPma := @MycpuBareSource.bootPma

variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (extra : IProp GF) : IProp GF :=
  iprop((∃ control, ⌜SieOffPacket.Ambient pc control⌝ ∗
      SieOffPacket.opened capacity fixed gen era cpu .identity ξ file available .bare control) ∗
    BareJal.code capacity era pc imm ∗ bootPma capacity era cpu ∗ extra)

noncomputable def kept (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (file : File) (available : Nat) (extra : IProp GF) : IProp GF :=
  iprop(KernelStack.own capacity.translation era .identity ξ (SieOffCapability.sp file) available ∗
    SieOffCapability.timer capacity era cpu ∗ SieOffCapability.tierWitness capacity era cpu .identity ∗
    Sconf.hardware capacity fixed gen era cpu ∗ SieOffPacket.slotToken capacity era cpu .bare ∗
    bootPma capacity era cpu ∗ extra)

noncomputable def resources (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (control : RegisterFile) (pc : BitVec 64) (imm : BitVec 21) (rr : Option Reservation)
    (extra : IProp GF) : IProp GF :=
  iprop(BareJal.packet capacity era cpu control file ∗ BareJal.code capacity era pc imm ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗
    kept capacity fixed gen era cpu ξ file available extra)

noncomputable def restored (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (codePC currentPC : BitVec 64) (imm : BitVec 21) (extra : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .identity ξ file available currentPC ∗
    BareJal.code capacity era codePC imm ∗ bootPma capacity era cpu ∗ extra)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (file : File) (available : Nat) (pc : BitVec 64) (imm : BitVec 21)
    (extra : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  iprop(restored capacity fixed gen era cpu ξ (afterFile pc file) available pc (KptJal.target pc imm) imm extra -∗
    ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)

end Xv6.Kernel.BareJalSource
