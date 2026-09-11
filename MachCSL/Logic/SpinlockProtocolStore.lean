import MachCSL.Logic.SpinlockProtocolRead
import MachCSL.Logic.MemoryWriteWPLink

namespace MachCSL.Logic.SpinlockProtocol
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- The existing full-ledger store pays the exact physical successor while
retaining all registers, devices and native heap metadata in the bundle. -/
theorem store_word [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (era : Era.Record) (g : State) (cpu : CPU) (req : EventPlan.WriteRequest 4)
    (old value : BitVec 32) (time : Nat) :
    iprop(⊢ MemoryWriteWP.writeBundle capacity.machine.era era g -∗
      Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes g -∗
      wordAt capacity era req.pa old time ==∗
      MemoryWriteWP.writeBundle capacity.machine.era era (MemoryWriteWP.writeState g cpu req value) ∗
      Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes
        (MemoryWriteWP.writeState g cpu req value) ∗
      Tso.History.logElem capacity.machine.era.history era.logEntries g.log.length
        ⟨snapshot req.pa 4 value, hartAgent cpu⟩ ∗
      wordAt capacity era req.pa value (g.log.length + 1)) := by
  iintro Hbundle Htso Hword
  ihave Hledger := wordAt_ledger capacity era req.pa old time $$ Hword
  unfold wordAt storeCapacity storeNames
  iapply MemoryWriteWP.bundle_store capacity.machine (MemoryWriteWP.nativeContracts capacity.machine)
    era g cpu 4 req old value (by decide) $$ Hbundle Htso Hledger

/-- Both actual request-kind classifications reduce to the source node view rule. -/
theorem swap_post_view (g : State) (cpu : CPU) :
    MemoryWriteWP.postView g cpu swapWrite = g.log.length + 1 := rfl

theorem counter_post_view (g : State) (cpu : CPU) (v : BitVec 32) :
    MemoryWriteWP.postView g cpu (counterWrite v) = g.views cpu := rfl

theorem unlock_post_view (g : State) (cpu : CPU) :
    MemoryWriteWP.postView g cpu unlockWrite = g.views cpu := rfl

end MachCSL.Logic.SpinlockProtocol
