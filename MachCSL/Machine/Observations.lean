import MachCSL.Machine.Reachability
import MachCSL.Machine.DevicePreservation

/-! Observable-history vocabulary from `iris/ObsTrace.v` at the pinned paper
revision. Histories retain interleaved input, output and power events. Output
projection is only a proof-side connection to the physical UART wire. -/
namespace MachCSL.Machine

def isIO : Observation → Bool
  | .uartIn _ | .uartOut _ => true
  | _ => false

def observationStep : Option Bool → Observation → Option Bool
  | some false, .powerOn => some true
  | some true, .powerOff => some false
  | some true, .uartIn _ | some true, .uartOut _ => some true
  | _, _ => none

def TraceShape (history : List Observation) (on : Bool) : Prop :=
  history.foldl observationStep (some false) = some on

def bootCount : List Observation → Nat
  | [] => 0
  | .powerOn :: rest => bootCount rest + 1
  | _ :: rest => bootCount rest

def segmentStep (segment : List Observation) : Observation → List Observation
  | .powerOn | .powerOff => []
  | event => segment ++ [event]

def openSegment (history : List Observation) : List Observation := history.foldl segmentStep []

def ObservationsOK (history : List Observation) (g : State) : Prop :=
  TraceShape history g.power ∧
  bootCount history = g.generation + (if g.power then 1 else 0) ∧
  (g.power = true → outputBytes (openSegment history) = g.devices.uart.wire)

theorem traceShape_nil : TraceShape [] false := rfl

theorem traceShape_snoc (history : List Observation) (event : Observation) (on next : Bool)
    (shape : TraceShape history on) (step : observationStep (some on) event = some next) :
    TraceShape (history ++ [event]) next := by
  unfold TraceShape at shape ⊢
  simpa [List.foldl_append, shape] using step

theorem traceShape_io (history events : List Observation) (shape : TraceShape history true)
    (io : ∀ e ∈ events, isIO e = true) : TraceShape (history ++ events) true := by
  have scan : events.foldl observationStep (some true) = some true := by
    induction events with
    | nil => rfl
    | cons e rest ih =>
      have he := io e (by simp)
      have hr := ih (fun x hx => io x (by simp [hx]))
      cases e <;> simp_all [isIO, observationStep]
  unfold TraceShape at shape ⊢
  simpa [List.foldl_append, shape] using scan

theorem bootCount_append (left right : List Observation) :
    bootCount (left ++ right) = bootCount left + bootCount right := by
  induction left with
  | nil => simp [bootCount]
  | cons e rest ih => cases e <;> simp [bootCount, ih, Nat.add_comm, Nat.add_left_comm]

theorem bootCount_io (events : List Observation) (io : ∀ e ∈ events, isIO e = true) :
    bootCount events = 0 := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    have he := io e (by simp)
    have hr := ih (fun x hx => io x (by simp [hx]))
    cases e <;> simp_all [isIO, bootCount]

theorem openSegment_append (history events : List Observation) :
    openSegment (history ++ events) = events.foldl segmentStep (openSegment history) := by
  simp [openSegment, List.foldl_append]

theorem segmentStep_io (segment events : List Observation) (io : ∀ e ∈ events, isIO e = true) :
    events.foldl segmentStep segment = segment ++ events := by
  induction events generalizing segment with
  | nil => simp
  | cons e rest ih =>
    have he := io e (by simp)
    have hr : ∀ x ∈ rest, isIO x = true := fun x hx => io x (by simp [hx])
    cases e <;> simp_all [isIO, segmentStep, List.append_assoc]

theorem openSegment_io (history events : List Observation) (io : ∀ e ∈ events, isIO e = true) :
    openSegment (history ++ events) = openSegment history ++ events := by
  rw [openSegment_append, segmentStep_io _ _ io]

theorem openSegment_power (history : List Observation) (event : Observation)
    (power : isIO event = false) : openSegment (history ++ [event]) = [] := by
  cases event <;> simp_all [isIO, openSegment_append, segmentStep]

theorem uart_observations_io (d d' : Devices.State) (events : List Observation)
    (step : UartStep d events d') : ∀ e ∈ events, isIO e = true := by
  cases step with
  | tx byte next pop => cases Devices.Uart.loopback d.uart <;> simp [isIO]
  | rx => simp [isIO]
  | latch => simp
  | idle => simp

theorem observations_init (g : State) (off : g.power = false) (zero : g.generation = 0) :
    ObservationsOK [] g := by
  simp [ObservationsOK, TraceShape, bootCount, off, zero]

theorem step_observations_ok [Platform] (image : BootImage) (e e' : Expr) (g g' : State)
    (events forks) (history : List Observation) (initial : ObservationsOK history g)
    (step : Step image e g events e' g' forks) : ObservationsOK (history ++ events) g' := by
  obtain ⟨shape, boots, wire⟩ := initial
  cases step with
  | hartLive generation cpu m m' g g' live h =>
    rw [List.append_nil]
    exact ⟨by simpa [hart_power _ _ _ _ _ h] using shape,
      by simpa [hart_power _ _ _ _ _ h, hart_generation _ _ _ _ _ h] using boots,
      fun on => by rw [hart_wire _ _ _ _ _ h]; exact wire ((hart_power _ _ _ _ _ h) ▸ on)⟩
  | hartDead => simpa [ObservationsOK] using And.intro shape (And.intro boots wire)
  | uartLive generation g events next live h =>
    have io := uart_observations_io _ _ _ h
    refine ⟨?_, ?_, ?_⟩
    · simpa [live.1] using traceShape_io history events (by simpa [live.1] using shape) io
    · simpa [bootCount_append, bootCount_io events io] using boots
    · intro on
      rw [openSegment_io history events io, outputBytes_append, wire on]
      exact (uart_wire _ _ _ h).symm
  | uartDead => simpa [ObservationsOK] using And.intro shape (And.intro boots wire)
  | diskLive generation g next writes log live h publish reserved =>
    rw [List.append_nil]
    exact ⟨shape, boots, fun on => by rw [disk_uart _ _ _ _ h]; exact wire on⟩
  | diskDead => simpa [ObservationsOK] using And.intro shape (And.intro boots wire)
  | plicLive => simpa [ObservationsOK] using And.intro shape (And.intro boots wire)
  | plicDead => simpa [ObservationsOK] using And.intro shape (And.intro boots wire)
  | power g events next forks h =>
    cases h with
    | off on =>
      refine ⟨traceShape_snoc history .powerOff true false (by simpa [on] using shape) rfl, ?_, ?_⟩
      · simpa [powerOff, bootCount_append, bootCount, on] using boots
      · intro impossible
        contradiction
    | on off next boot =>
      have on := boot.2.2.1
      have uart := boot.2.2.2.2.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [on]
        exact traceShape_snoc history .powerOn false true (by simpa [off] using shape) rfl
      · simp only [bootCount_append, bootCount, Nat.zero_add, on, ↓reduceIte, boot.1]
        simpa [off] using boots
      · intro _
        rw [openSegment_power history .powerOn rfl, uart]
        rfl

theorem poolStep_observations_ok [Platform] (image : BootImage)
    (before after : Configuration) (events history : List Observation)
    (initial : ObservationsOK history before.2) (step : PoolStep image before events after) :
    ObservationsOK (history ++ events) after.2 := by
  cases step with
  | atomic h left right => exact step_observations_ok image _ _ _ _ _ _ history initial h

theorem poolSteps_observations_ok [Platform] (image : BootImage) (n : Nat)
    (before after : Configuration) (events history : List Observation)
    (initial : ObservationsOK history before.2) (steps : PoolSteps image n before events after) :
    ObservationsOK (history ++ events) after.2 := by
  induction steps generalizing history with
  | refl => simpa using initial
  | cons first rest ih =>
    rw [← List.append_assoc]
    exact ih _ (poolStep_observations_ok image _ _ _ _ initial first)

/-- Every finite schedule from the initial off state has the source trace
shape, boot count and current-cycle UART wire correspondence. Content and
per-cycle protocol correctness still require the client ownership proof. -/
theorem run_observations_ok [Platform] (image : BootImage) (n : Nat)
    (threads threads' : List Expr) (g g' : State) (events : List Observation)
    (off : g.power = false) (zero : g.generation = 0)
    (steps : PoolSteps image n (threads, g) events (threads', g')) : ObservationsOK events g' :=
  poolSteps_observations_ok image n _ _ events [] (observations_init g off zero) steps

end MachCSL.Machine
