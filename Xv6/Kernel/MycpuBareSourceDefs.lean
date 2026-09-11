import Xv6.Kernel.SieOffPacketDefs
import Xv6.Kernel.MycpuOffDefs
import Xv6.Kernel.KernelDatumWordDefs
import Xv6.Kernel.KernelTextImageDefs

/-! The identity-tier Bare arm of the actual disabled source packet.
The identity tier alone does not select this arm. Its three translation
cells come from the opened Bare slot, never from an unowned file projection. -/
namespace Xv6.Kernel.MycpuBareSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev sp := SieOffCapability.sp

def entryPC : BitVec 64 := MycpuDecode.address ⟨0, by decide⟩
def returnPC (cpu : CPU) (original : File) : BitVec 64 :=
  MycpuReturn.retPC (HartTp.rget cpu original 1#5)

def bareCapacity {GF : BundledGFunctors} (capacity : Capacity GF) : MycpuOff.Capacity GF :=
  ⟨capacity.machine, capacity.bits⟩

def shares : MycpuOff.Shares :=
  ⟨.own 1, .own 1, ⟨.discard, .own 1, .own 1, .discard⟩,
    .discard, .own 1, .own 1, .own 1, .discard, .own 1⟩

/-- Only these three values are supplied by the actual existential Bare
slot. All other control projections retain their original interpretation. -/
def patch (control : RegisterFile) (satp : BitVec 64) (pmp : RegisterFile) : RegisterFile := fun r =>
  match r with
  | .satp => satp
  | .pmpcfg_n => pmp .pmpcfg_n
  | .pmpaddr_n => pmp .pmpaddr_n
  | other => control other

def Result (cpu : CPU) (original after : File) : Prop :=
  MycpuOff.Saved original after ∧
    after 10#5 = MycpuScalar.mycpuRet (HartTp.rget cpu original 4#5)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev bootPma (era : Era.Record) (cpu : CPU) : IProp GF :=
  Registers.regPointsto capacity.machine.era.registers (era.registers cpu)
    .pma_regions .discard pmaBoot

def physicalPair (era : Era.Record) (ξ : TsoContext.CtxId) (entrySP : BitVec 64)
    (raWord s0Word : BitVec 64) : IProp GF :=
  iprop(TsoContextReadWP.wordPointsto capacity.machine era ξ (KernelStack.paStk entrySP 1) (.own 1) raWord ∗
    TsoContextReadWP.wordPointsto capacity.machine era ξ (KernelStack.paStk entrySP 2) (.own 1) s0Word)

/-- Closing wands retain the original virtual mapping claims and accept
the actual newly stored contents, including their updated timestamps. -/
def closeWord (era : Era.Record) (ξ : TsoContext.CtxId) (address : BitVec 64) : IProp GF :=
  iprop(∀ word, TsoContextReadWP.wordPointsto capacity.machine era ξ address (.own 1) word -∗
    KernelDatum.word capacity.translation era .identity ξ address (.own 1) word)

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Exactly the Bare disjunct yielded by SieOffPacket.open_packet, with
its already-derived ambient facts. A later dispatcher handles the KPT arm. -/
noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (original : File) (available : Nat) (extra : IProp GF) : IProp GF :=
  iprop((∃ control, ⌜SieOffPacket.Ambient entryPC control⌝ ∗
      SieOffPacket.opened capacity fixed gen era cpu .identity ξ original available .bare control) ∗
    KernelTextImage.text capacity.translation era .identity ∗ bootPma capacity era cpu ∗ extra)

noncomputable def frame (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (available : Nat) (extra : IProp GF) : IProp GF :=
  iprop(KernelStack.own capacity.translation era .identity ξ (KernelStack.paStk entrySP 2) (available - 2) ∗
    closeWord capacity era ξ (KernelStack.paStk entrySP 1) ∗
    closeWord capacity era ξ (KernelStack.paStk entrySP 2) ∗
    SieOffCapability.timer capacity era cpu ∗ SieOffCapability.tierWitness capacity era cpu .identity ∗
    Sconf.hardware capacity fixed gen era cpu ∗ SieOffPacket.slotToken capacity era cpu .bare ∗
    KernelTextImage.text capacity.translation era .identity ∗ bootPma capacity era cpu ∗ extra)

noncomputable def resources (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (available : Nat)
    (control : RegisterFile) (file : File) (raWord s0Word : BitVec 64)
    (rr : Option Reservation) (extra : IProp GF) : IProp GF :=
  iprop(MycpuOff.resources (bareCapacity capacity) era cpu control file shares ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗ MycpuBare.shared capacity.machine era ∗
    physicalPair capacity era ξ entrySP raWord s0Word ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗
    frame capacity fixed gen era cpu ξ entrySP available extra)

noncomputable def restored (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (file : File) (available : Nat) (pc : BitVec 64)
    (extra : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .identity ξ file available pc ∗
    KernelTextImage.text capacity.translation era .identity ∗ bootPma capacity era cpu ∗ extra)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (original : File) (available : Nat) (extra : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ after, ⌜Result cpu original after⌝ -∗
    restored capacity fixed gen era cpu ξ after available (returnPC cpu original) extra -∗
    ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)

end Xv6.Kernel.MycpuBareSource
