import Xv6.Kernel.PushOffStackDefs

namespace Xv6.Kernel.PushOffStack
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} (capacity : Capacity GF)

def packetFrame (era : Era.Record) (cpu : CPU) (control : RegisterFile)
    (values : File) (s : Shares) (slot : Slot) : IProp GF :=
  iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry control cpu values) (remainderFootprint s slot) ∗
    MycpuRegimeShell.bitFrame capacity era cpu (control .mstatus) ∗ ⌜values 0#5 = 0#64⌝)

def tail (kind : Kind) (slot : Slot) : KptMemory.Result kind → SailM ExecutionResult :=
  match kind with | .load => loadTail slot | .store => storeTail

namespace Kpt
abbrev guards := @MycpuKptMemory.guards
variable {hlc : HasLC} [InvGS_gen hlc GF]
noncomputable def resources (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : HartTp.GprFile)
    (shares : Shares) (N : Namespace) (root : PtTree.PPN) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 64) (rr : Option Reservation)
    (outcome : KptAddress.Outcome) (view : Nat) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) control (afterMap kind slot values old) shares ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    KernelDatum.word capacity.translation era tier ξ (address cpu values slot) dq
      (KptMemory.valueAfter kind old (sourceValue cpu values slot)) ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
      (KptMemory.afterReservation kind (address cpu values slot) rr outcome) ∗
    KptAddress.receipts capacity.translation era cpu (address cpu values slot) outcome ∗
    Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view ∗ frame)

noncomputable def continueWith [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : HartTp.GprFile)
    (shares : Shares) (N : Namespace) (root : PtTree.PPN) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 64) (rr : Option Reservation)
    (frame : IProp GF) (continuation : ExecutionResult → SailM Unit) (post : Empty → IProp GF) (ppn : PtTree.PPN) (data : KptAddress.Data) (outcome : KptAddress.Outcome) : IProp GF :=
  iprop(
    ⌜KptMemory.CompletedFacts (entry control cpu values) data root kind (address cpu values slot) ppn outcome⌝ -∗
    ▷ (∀ view, resources capacity era cpu control values shares N root kind slot tier ξ dq old rr outcome view frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (continuation (.Retire_Success ()))) post))

noncomputable def finish [Platform]
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (control : RegisterFile) (values : HartTp.GprFile)
    (shares : Shares) (N : Namespace) (root : PtTree.PPN) (kind : Kind) (slot : Slot)
    (tier : Tier) (ξ : TsoContext.CtxId) (dq : DFrac) (old : BitVec 64) (rr : Option Reservation)
    (frame : IProp GF) (continuation : ExecutionResult → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  guards (continueWith capacity image fixed whole gen era cpu control values shares N root kind slot tier ξ dq old rr frame continuation post)

end Kpt

end Xv6.Kernel.PushOffStack
