import MachCSL.Logic.DeviceDefs
import MachCSL.Logic.RegisterDefs

namespace MachCSL.Logic.Device
open Iris MachCSL.Devices

def uartFunctor : GFunctor := ⟨GhostVarF Uart.State, inferInstance⟩
def plicFunctor : GFunctor := ⟨GhostVarF Plic.State, inferInstance⟩
def virtioFunctor : GFunctor := ⟨GhostVarF Virtio.State, inferInstance⟩

inductive Slot where
  | uart
  | plic
  | virtio
  deriving DecidableEq
def Slot.index : Slot → Nat
  | .uart => 7
  | .plic => 8
  | .virtio => 9

theorem Slot.index_injective {a b : Slot} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [index]

/-- The three device cameras extend the shared register/TSO registry. -/
def registry : BundledGFunctors :=
  ((Registers.registry.set Slot.uart.index uartFunctor).set Slot.plic.index plicFunctor).set
    Slot.virtio.index virtioFunctor

theorem registry_old (i : Nat) (h : i < 7) : registry i = Registers.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 7 by omega,
    show i ≠ 8 by omega, show i ≠ 9 by omega]

theorem registry_unused (i : Nat) (h : 10 ≤ i) : registry i = Registers.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 7 by omega,
    show i ≠ 8 by omega, show i ≠ 9 by omega]

def registryCapacity : Capacity registry :=
  ⟨{ elemG := ⟨7, rfl⟩ }, { elemG := ⟨8, rfl⟩ }, { elemG := ⟨9, rfl⟩ }⟩
def registerCapacity : Registers.Capacity registry := ⟨⟨⟨6, rfl⟩⟩⟩
def historyCapacity : Tso.History.Capacity registry := ⟨⟨⟨4, rfl⟩⟩, ⟨5, rfl⟩⟩
def viewsCapacity : Tso.Views.Capacity registry := ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩
def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩

end MachCSL.Logic.Device
