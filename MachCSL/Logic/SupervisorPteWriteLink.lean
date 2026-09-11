import MachCSL.Logic.SupervisorPteWriteProofs

namespace MachCSL.Logic.SupervisorPteWrite
open Iris MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions

/-- Native partial-register and pinned-memory rules discharge the full checked
conditional PTE wrapper, without a supplied software contract or payer. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

/-- The exact authored append, top view and cleared own reservation, with all
other machine fields framed, are equations of the actual event successor. -/
theorem event_effect (g : State) (cpu : CPU) (address word : BitVec 64) :
    TsoPinnedWriteWP.Effect g (MemoryWriteWP.writeState g cpu (request address word) word)
      cpu (request address word) word :=
  TsoPinnedWriteWP.write_effect g cpu (request address word) word rfl

/-- Neither the checked wrapper nor the resource contract imposes disjointness
from other reservations. The actual blocked and committed arms remain visible. -/
theorem event_step_inv [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (address word : BitVec 64) (range : SupervisorPhysical.RamRange address 8)
    (k : MemoryWriteWP.WriteResult → SailM Unit) (live : ThreadLive g gen)
    (events : List Observation) (next : Expr) (after : State) (forks : List Expr)
    (step : Step image (.hart gen cpu (.impure (.writeMem 8 (request address word)) k))
      g events next after forks) :
    (¬Disjoint (Footprint address 8) (othersReserved g.reservations cpu) ∧
      next = .hart gen cpu (.impure (.writeMem 8 (request address word)) k) ∧
      after = g ∧ forks = [] ∧ events = []) ∨
    (Disjoint (Footprint address 8) (othersReserved g.reservations cpu) ∧
      next = .hart gen cpu (k (.Ok none)) ∧
      after = MemoryWriteWP.writeState g cpu (request address word) word ∧
      TsoPinnedWriteWP.Effect g after cpu (request address word) word ∧ forks = [] ∧ events = []) :=
  TsoPinnedWriteWP.step_inv image g gen cpu (request address word) word k rfl
    (request_ram address word range) rfl live events next after forks step

end MachCSL.Logic.SupervisorPteWrite
