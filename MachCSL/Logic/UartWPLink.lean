import MachCSL.Logic.UartWPProofs
import MachCSL.Logic.UartGhostRegistry

namespace MachCSL.Logic.UartWP
open Iris Iris.BI MachCSL.Machine

theorem registryUartWPSpec [Platform] (invariants : Invariant.Names) :
    letI := UartGhost.nativeInvariant invariants
    UartWPSpec UartGhost.machineCapacity UartGhost.registryCapacity := by
  letI := UartGhost.nativeInvariant invariants
  exact uartWPSpec UartGhost.machineCapacity UartGhost.registryCapacity

/-- The concrete 23-slot registry discharges all ghost and machine-state
component proofs. Only the stated native invariants and source trace permit
remain as client resources. -/
theorem registry_wp_uart_loop [Platform] (invariants : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (Nuart Nplic : Namespace)
    (names : UartGhost.Names) (post : Empty → IProp UartGhost.registry) :
    letI := UartGhost.nativeInvariant invariants
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed generation era -∗
      uartInv UartGhost.machineCapacity UartGhost.registryCapacity Nuart era names -∗
      plicInv UartGhost.machineCapacity Nplic era -∗
      obsPermit UartGhost.machineCapacity UartGhost.registryCapacity Nuart fixed.observations names -∗
      DeadThread.threadWP UartGhost.machineCapacity image fixed whole (.uart generation) post) := by
  letI := UartGhost.nativeInvariant invariants
  exact wp_uart_loop UartGhost.machineCapacity UartGhost.registryCapacity image fixed whole generation era Nuart Nplic names post

theorem registry_wp_uart_loop_trivial [Platform] (invariants : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (Nuart Nplic Nobs : Namespace)
    (names : UartGhost.Names) (post : Empty → IProp UartGhost.registry)
    (mask : (↑Nobs : CoPset) ⊆ ⊤ \ ↑Nuart) :
    letI := UartGhost.nativeInvariant invariants
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed generation era -∗
      uartInv UartGhost.machineCapacity UartGhost.registryCapacity Nuart era names -∗
      plicInv UartGhost.machineCapacity Nplic era -∗
      ObservationInvariant.trivial UartGhost.machineCapacity.power Nobs fixed.observations -∗
      DeadThread.threadWP UartGhost.machineCapacity image fixed whole (.uart generation) post) := by
  letI := UartGhost.nativeInvariant invariants
  exact wp_uart_loop_trivial UartGhost.machineCapacity UartGhost.registryCapacity image fixed whole generation era Nuart Nplic Nobs names post mask

end MachCSL.Logic.UartWP
