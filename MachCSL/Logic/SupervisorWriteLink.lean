import MachCSL.Logic.SupervisorWriteProofs

namespace MachCSL.Logic.SupervisorWrite
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

/-- Existing native capacities construct the complete checked-store contract. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

/-- Exact event successor: one authored write, all CPU views unchanged, only the
own reservation cleared, with registers, devices and full world fields framed. -/
theorem event_effect (g : State) (cpu : CPU) (address word : BitVec 64) :
    TsoContextWriteWP.Effect g (MemoryWriteWP.writeState g cpu (request address word) word)
      cpu (request address word) word :=
  TsoContextWriteWP.write_effect g cpu (request address word) word (by rfl)

/-- Both actual live write-node cases remain possible. The public WP requires
no global disjointness premise; the native rule repeats the exact blocked node. -/
theorem event_step_inv [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (address word : BitVec 64) (range : SupervisorPhysical.RamRange address 8)
    (k : MemoryWriteWP.WriteResult → SailM Unit) (live : ThreadLive g gen)
    (events : List Observation) (next : Expr) (after : State) (forks : List Expr)
    (step : Step image (.hart gen cpu (.impure (.writeMem 8 (request address word)) k))
      g events next after forks) :
    (¬Memory.Disjoint (Memory.Footprint address 8) (othersReserved g.reservations cpu) ∧
      next = .hart gen cpu (.impure (.writeMem 8 (request address word)) k) ∧
      after = g ∧ forks = [] ∧ events = []) ∨
    (Memory.Disjoint (Memory.Footprint address 8) (othersReserved g.reservations cpu) ∧
      next = .hart gen cpu (k (.Ok none)) ∧
      after = MemoryWriteWP.writeState g cpu (request address word) word ∧
      TsoContextWriteWP.Effect g after cpu (request address word) word ∧ forks = [] ∧ events = []) :=
  TsoContextWriteWP.step_inv image g gen cpu (request address word) word k rfl
    (request_ram address word range) (by rfl) live events next after forks step

end MachCSL.Logic.SupervisorWrite
