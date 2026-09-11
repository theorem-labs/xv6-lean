import MachCSL.Logic.RestartWPProofs
import MachCSL.Logic.UartGhostRegistry

namespace MachCSL.Logic.RestartWP
open Iris Iris.BI MachCSL.Machine

theorem registryRestartWPSpec [Platform] (invariants : Invariant.Names) :
    letI := UartGhost.nativeInvariant invariants
    RestartWPSpec UartGhost.machineCapacity := by
  letI := UartGhost.nativeInvariant invariants
  exact restartWPSpec UartGhost.machineCapacity

theorem registry_wp_restart [Platform] (invariants : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (post : Empty → IProp UartGhost.registry) :
    letI := UartGhost.nativeInvariant invariants
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed generation era -∗
      Reservations.resvAny UartGhost.machineCapacity.era.reservations era.reservations cpu -∗
      ▷ (∀ tick : Bool, Reservations.resvFrag UartGhost.machineCapacity.era.reservations era.reservations cpu none -∗
        DeadThread.threadWP UartGhost.machineCapacity image fixed whole (.hart generation cpu (cycle tick)) post) -∗
      DeadThread.threadWP UartGhost.machineCapacity image fixed whole (.hart generation cpu (.pure ())) post) := by
  letI := UartGhost.nativeInvariant invariants
  exact wp_restart UartGhost.machineCapacity image fixed whole generation era cpu post

end MachCSL.Logic.RestartWP
