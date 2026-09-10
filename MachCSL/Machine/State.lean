import MachCSL.Machine.NodeProofs
import MachCSL.Machine.Platform
import MachCSL.Devices.Fabric

/-! Eight-hart global state and reservation invariants, from
`iris/RiscvLang.v:gstate,mm_ok,resv_ok,hart_node_step`. -/
namespace MachCSL.Machine
open Memory

structure State where
  registers : CPU → RegisterFile
  memory : ByteMap 64
  devices : Devices.State
  generation : Nat
  power : Bool
  reservations : CPU → Option Reservation
  image : ByteMap 64
  log : WriteLog 64
  views : CPU → Nat

def updateHart (files : CPU → α) (cpu : CPU) (value : α) : CPU → α :=
  fun other => if other = cpu then value else files other

def reservationDomain (reservations : CPU → Option Reservation) (cpu : CPU)
    (address : PhysicalAddress) : Prop :=
  ∃ r, reservations cpu = some r ∧ Domain r address

def othersReserved (reservations : CPU → Option Reservation) (cpu : CPU)
    (address : PhysicalAddress) : Prop :=
  ∃ other, other ≠ cpu ∧ reservationDomain reservations other address

def allReserved (reservations : CPU → Option Reservation) (address : PhysicalAddress) : Prop :=
  ∃ cpu, reservationDomain reservations cpu address

def MemoryOK (g : State) : Prop :=
  g.memory = flat g.image g.log ∧ (∀ cpu, g.views cpu ≤ g.log.length) ∧
    ∀ a, ramLow ≤ a.toNat → a.toNat < ramHigh → Domain g.image a

def ReservationsOK (g : State) : Prop :=
  ∀ cpu r, g.reservations cpu = some r → Submap r g.memory

def ThreadLive (g : State) (generation : Nat) : Prop :=
  g.power = true ∧ g.generation = generation

def focus (g : State) (cpu : CPU) : LocalState Devices.State :=
  ⟨g.registers cpu, g.memory, g.devices, g.log, g.views cpu, g.reservations cpu⟩

def writeBack (g : State) (cpu : CPU) (after : LocalState Devices.State) : State :=
  { g with
    registers := updateHart g.registers cpu after.registers
    memory := after.memory
    devices := after.devices
    reservations := updateHart g.reservations cpu after.reservation
    log := after.log
    views := updateHart g.views cpu after.view }

def HartStep [Platform] (g : State) (cpu : CPU) (m m' : SailM Unit) (g' : State) : Prop :=
  ∃ after, NodeStep Devices.bus (othersReserved g.reservations cpu) (hartAgent cpu)
    g.image (focus g cpu) m m' after ∧ g' = writeBack g cpu after

theorem focus_writeBack (g : State) (cpu : CPU) (after : LocalState Devices.State) :
    focus (writeBack g cpu after) cpu = after := by
  cases after
  simp [focus, writeBack, updateHart]

theorem hart_generation [Platform] (g g' : State) (cpu : CPU) (m m' : SailM Unit)
    (step : HartStep g cpu m m' g') : g'.generation = g.generation := by
  obtain ⟨after, _, rfl⟩ := step
  rfl

theorem hart_power [Platform] (g g' : State) (cpu : CPU) (m m' : SailM Unit)
    (step : HartStep g cpu m m' g') : g'.power = g.power := by
  obtain ⟨after, _, rfl⟩ := step
  rfl

theorem hart_flat [Platform] (g g' : State) (cpu : CPU) (m m' : SailM Unit)
    (initial : g.memory = flat g.image g.log) (step : HartStep g cpu m m' g') :
    g'.memory = flat g'.image g'.log := by
  obtain ⟨after, step, rfl⟩ := step
  exact node_flat_preserved Devices.bus _ _ g.image (focus g cpu) after m m' initial step

end MachCSL.Machine
