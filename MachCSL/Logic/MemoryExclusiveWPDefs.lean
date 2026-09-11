import MachCSL.Logic.MemoryReadWPDefs

/-! Exclusive RAM reads from HartEvents.v. The full dependent request remains
an argument; the leaf introduces no alignment, no-wrap, or small-width guard. -/
namespace MachCSL.Logic.MemoryExclusiveWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
abbrev ReadRequest := MemoryReadWP.ReadRequest
abbrev ReadResult := MemoryReadWP.ReadResult
abbrev threadWP := @DeadThread.threadWP

def reserve (g : State) (cpu : CPU) (value : Option Reservation) : State :=
  { g with reservations := updateHart g.reservations cpu value }

def acquired (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) : State :=
  reserve (TsoRead.advanceView g cpu g.log.length) cpu (some (snapshot a n word))

/-- Native counterpart of the source mstate bundle, at global-register
granularity. Disk, reservation, and fixed authorities stay outside the callback. -/
def readBundle {GF : BundledGFunctors} (capacity : Era.Capacity GF) (era : Era.Record)
    (g : State) : IProp GF :=
  iprop(GlobalRegisters.gregsInterp capacity.registers era.registers g.registers ∗
    Era.heapInterpAt capacity era g ∗ Device.interp capacity.devices era.deviceNames g.devices)

/-- Source exclusive-read callback: view authority is already at the log top.
It must return the same physical bundle and advanced TSO interpretation; the
rule itself updates the reservation and reassembles the complete successor. -/
def exclusivePremise {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : ReadRequest n) (k : ReadResult n → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ g : State, readBundle capacity.era era g -∗
    Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes
      (TsoRead.advanceView g cpu g.log.length) -∗
    Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) g.log.length ={⊤,∅}=∗
    ∃ word : BitVec (8 * n), ⌜readBytes g.memory req.pa n = some word⌝ ∗
      ▷ (|={∅,⊤}=> readBundle capacity.era era g ∗
        Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes
          (TsoRead.advanceView g cpu g.log.length) ∗
        (Reservations.resvFrag capacity.era.reservations era.reservations cpu
          (some (snapshot req.pa n word)) -∗
          threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post)))

end MachCSL.Logic.MemoryExclusiveWP
