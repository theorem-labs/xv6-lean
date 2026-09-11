import MachCSL.Machine.JalLoopStep

/-! Both clock choices and finite repetition through the actual pure-node restart.
The fetch premise is discharged by the separate boot-snapshot certificate. -/
namespace MachCSL.Machine.JalLoop
open LeanPaperStock.Functions

abbrev Fetches [Platform] (cpu : CPU) : Prop := ∀ d : Dynamic,
  FetchExec (loadedRam jalImage) (fetch ()) (registers cpu d)
    (.F_Base 0x6f#32) (registers cpu d)

theorem cycle_fromFetch [Platform] (cpu : CPU) (d : Dynamic) (tick : Bool)
    (fetches : Fetches cpu) :
    FetchExec (loadedRam jalImage) (cycle tick) (registers cpu d)
      () (registers cpu (afterCycle tick d)) := by
  unfold cycle
  refine (try_step_fromFetch cpu d (fetches (enableIncrement d))).bind ?_
  cases tick with
  | false => exact ((registerExec_pure _ _ _).mpr rfl).fetchExec _
  | true => exact (tick_clock_registers cpu (retire d)).fetchExec _

theorem cycle_nodeSteps_fromFetch [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent)
    (image : Memory.ByteMap 64) (state : LocalState Device)
    (cpu : CPU) (d : Dynamic) (tick : Bool) (fetches : Fetches cpu)
    (canonical : state.registers = registers cpu d)
    (hview : state.view ≤ state.log.length)
    (hread : ∀ a, loadedRam jalImage a = Memory.read image state.log hart state.view a) :
    NodeSteps bus others hart image (cycle tick) state (.pure ())
      {state with registers := registers cpu (afterCycle tick d)} := by
  apply fetchExec_nodeSteps bus others hart image (loadedRam jalImage) state _ _ hview hread
  rw [canonical]
  exact cycle_fromFetch cpu d tick fetches

private theorem nodeSteps_trans [Platform] (bus : Bus Device) (others) (hart) (image)
    {program middle last : SailM Unit} {before between after : LocalState Device}
    (first : NodeSteps bus others hart image program before middle between)
    (rest : NodeSteps bus others hart image middle between last after) :
    NodeSteps bus others hart image program before last after := by
  induction first with
  | nil => exact rest
  | cons step _ ih => exact .cons step (ih rest)

def afterTick (state : LocalState Device) (cpu : CPU) (d : Dynamic) (tick : Bool) :
    LocalState Device :=
  {state with registers := registers cpu (afterCycle tick d), reservation := none}

def afterTicks (state : LocalState Device) (cpu : CPU) (d : Dynamic) :
    List Bool → LocalState Device
  | [] => state
  | tick :: rest => afterTicks (afterTick state cpu d tick) cpu (afterCycle tick d) rest

/-- Every finite Boolean list is admitted. Each iteration includes a real
restart event and clears the reservation exactly where the source requires it.
This is a finite local witness, not a restriction on global scheduling. -/
theorem repeat_nodeSteps_fromFetch [Platform] (bus : Bus Device)
    (others : Memory.PhysicalAddress → Prop) (hart : Memory.Agent)
    (image : Memory.ByteMap 64) (cpu : CPU) (fetches : Fetches cpu)
    (ticks : List Bool) (state : LocalState Device) (d : Dynamic)
    (canonical : state.registers = registers cpu d)
    (hview : state.view ≤ state.log.length)
    (hread : ∀ a, loadedRam jalImage a = Memory.read image state.log hart state.view a) :
    NodeSteps bus others hart image (.pure ()) state (.pure ()) (afterTicks state cpu d ticks) := by
  induction ticks generalizing state d with
  | nil => exact .nil _ _
  | cons tick rest ih =>
    apply NodeSteps.cons (restart_step bus others hart image state tick)
    have cycleSteps := cycle_nodeSteps_fromFetch bus others hart image
      {state with reservation := none} cpu d tick fetches canonical hview hread
    apply nodeSteps_trans bus others hart image cycleSteps
    exact ih (afterTick state cpu d tick) (afterCycle tick d) rfl hview hread

end MachCSL.Machine.JalLoop
