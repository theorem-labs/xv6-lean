import MachCSL.Machine.SpinlockPoolRegisters
import MachCSL.Machine.JalDevicesProofs

/-! Actual worker frames for the concrete spinlock annotation. The pool and
all cursor labels are retained; no worker preservation callback is assumed. -/
namespace MachCSL.Machine.SpinlockPool
open Memory

theorem devices_frame {pool : Pool} {g : State} (next : Devices.State)
    (reset : ResetVirtio g → ∃ previous, next.virtio = Devices.Virtio.virtio_reset previous)
    (inv : PoolInv (pool, g)) : PoolInv (pool, { g with devices := next }) := by
  refine ⟨⟨inv.1.labels, inv.1.power, inv.1.generations, inv.1.current⟩, ?_⟩
  intro on
  obtain ⟨memory, reservations, image, oldReset, code, w, words, cursors, owner⟩ := inv.2 on
  exact ⟨memory, reservations, image, reset oldReset, code, w, words, cursors, owner⟩

theorem uart_frame {pool : Pool} {g : State} {events : List Observation} {next : Devices.State}
    (step : UartStep g.devices events next) (inv : PoolInv (pool, g)) :
    PoolInv (pool, { g with devices := next }) := by
  apply devices_frame next ?_ inv
  intro reset
  exact JalDevices.uart_preserves_reset g.devices next events reset step

theorem plic_frame {pool : Pool} {g : State} {files : CPU → RegisterFile}
    (step : PlicStep g.devices g.registers files) (inv : PoolInv (pool, g)) :
    PoolInv (pool, { g with registers := files }) := by
  refine ⟨⟨inv.1.labels, inv.1.power, inv.1.generations, inv.1.current⟩, ?_⟩
  intro on
  obtain ⟨memory, reservations, image, reset, code, w, words, cursors, owner⟩ := inv.2 on
  refine ⟨memory, reservations, image, reset, code, w, words, ?_, owner⟩
  intro gen cpu program c member live
  obtain ⟨control, phase⟩ := cursors gen cpu program c member live
  exact ⟨plic_control g files step cpu program c control, phase⟩

/-- Every UART primitive, including a stale worker, keeps the entire annotated
pool valid. Its actual observations remain those supplied by the language. -/
theorem uart_step_frame [Platform] {pool : Pool} {g g' : State} {gen : Nat}
    {events : List Observation} {next : Expr} {forks : List Expr}
    (step : Step SpinlockImage.image (.uart gen) g events next g' forks)
    (inv : PoolInv (pool, g)) :
    next = .uart gen ∧ forks = [] ∧ PoolInv (pool, g') := by
  cases step with
  | uartDead => exact ⟨rfl, rfl, inv⟩
  | uartLive generation g observations next live action =>
    exact ⟨rfl, rfl, uart_frame action inv⟩

theorem plic_step_frame [Platform] {pool : Pool} {g g' : State} {gen : Nat}
    {events : List Observation} {next : Expr} {forks : List Expr}
    (step : Step SpinlockImage.image (.plic gen) g events next g' forks)
    (inv : PoolInv (pool, g)) :
    next = .plic gen ∧ events = [] ∧ forks = [] ∧ PoolInv (pool, g') := by
  cases step with
  | plicDead => exact ⟨rfl, rfl, rfl, inv⟩
  | plicLive generation g registers live action =>
    exact ⟨rfl, rfl, rfl, plic_frame action inv⟩

/-- The live reset disk has no RAM/log/device change, even through the source
wild-write arm; stale disk workers also retain the state exactly. -/
theorem disk_step_frame [Platform] {pool : Pool} {g g' : State} {gen : Nat}
    {events : List Observation} {next : Expr} {forks : List Expr}
    (step : Step SpinlockImage.image (.disk gen) g events next g' forks)
    (inv : PoolInv (pool, g)) :
    next = .disk gen ∧ g' = g ∧ events = [] ∧ forks = [] ∧ PoolInv (pool, g') := by
  by_cases live : ThreadLive g gen
  · have reset : JalDevices.DiskReset g.devices := (inv.2 live.1).2.2.2.1
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      JalDevices.disk_thread_idle SpinlockImage.image gen g events next g' forks reset step
    exact ⟨rfl, rfl, rfl, rfl, inv⟩
  · cases step with
    | diskDead => exact ⟨rfl, rfl, rfl, rfl, inv⟩
    | diskLive generation g next writes log active action publish reserved =>
      exact False.elim (live active)

end MachCSL.Machine.SpinlockPool
