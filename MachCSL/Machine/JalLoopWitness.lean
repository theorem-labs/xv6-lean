import MachCSL.Machine.JalLoopCycles
import MachCSL.Machine.JalLoopFetch
import MachCSL.Machine.JalLoopProofs

/-! Unconditional canonical-family fetch/retirement/clock certificates for all
8 machine harts, and finite witnesses through the actual node relation.
These are local execution results; global scheduling and Iris WP are separate. -/
namespace MachCSL.Machine.JalLoop
open LeanPaperStock.Functions

theorem fetches [Platform] (cpu : CPU) : Fetches cpu := fetch_registers cpu

theorem try_step_registers [Platform] (cpu : CPU) (d : Dynamic) :
    FetchExec (loadedRam jalImage) (try_step 0 false) (registers cpu d)
      false (registers cpu (retire d)) :=
  try_step_fromFetch cpu d (fetch_registers cpu (enableIncrement d))

theorem cycle_registers [Platform] (cpu : CPU) (d : Dynamic) (tick : Bool) :
    FetchExec (loadedRam jalImage) (cycle tick) (registers cpu d)
      () (registers cpu (afterCycle tick d)) := cycle_fromFetch cpu d tick (fetches cpu)

theorem cycle_nodeSteps [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent)
    (image : Memory.ByteMap 64) (state : LocalState Device)
    (cpu : CPU) (d : Dynamic) (tick : Bool)
    (canonical : state.registers = registers cpu d)
    (hview : state.view ≤ state.log.length)
    (hread : ∀ a, loadedRam jalImage a = Memory.read image state.log hart state.view a) :
    NodeSteps bus others hart image (cycle tick) state (.pure ())
      {state with registers := registers cpu (afterCycle tick d)} :=
  cycle_nodeSteps_fromFetch bus others hart image state cpu d tick (fetches cpu) canonical hview hread

theorem repeat_nodeSteps [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent)
    (image : Memory.ByteMap 64) (cpu : CPU) (ticks : List Bool)
    (state : LocalState Device) (d : Dynamic)
    (canonical : state.registers = registers cpu d)
    (hview : state.view ≤ state.log.length)
    (hread : ∀ a, loadedRam jalImage a = Memory.read image state.log hart state.view a) :
    NodeSteps bus others hart image (.pure ()) state (.pure ()) (afterTicks state cpu d ticks) :=
  repeat_nodeSteps_fromFetch bus others hart image cpu (fetches cpu) ticks state d canonical hview hread

def bootLocalState (cpu : CPU) (devices : Device) : LocalState Device where
  registers := bootRegisters jalImage.vector (BitVec.ofNat 64 cpu.val)
  memory := loadedRam jalImage
  devices := devices
  log := []
  view := 0
  reservation := none

/-- A premise-free local witness for each real hart's generated boot result.
No claim about global interleavings or Iris weakest preconditions is made here. -/
theorem boot_repeat_nodeSteps [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (cpu : CPU) (devices : Device)
    (ticks : List Bool) :
    NodeSteps bus others (hartAgent cpu) (loadedRam jalImage) (.pure ())
      (bootLocalState cpu devices) (.pure ())
      (afterTicks (bootLocalState cpu devices) cpu
        (dynamic (bootRegisters jalImage.vector (BitVec.ofNat 64 cpu.val))) ticks) := by
  apply repeat_nodeSteps
  · exact (override_dynamic _).symm
  · exact Nat.le_refl 0
  · intro address
    rfl

end MachCSL.Machine.JalLoop
