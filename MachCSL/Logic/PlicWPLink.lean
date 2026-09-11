import MachCSL.Logic.PlicWPProofs
import MachCSL.Logic.UartGhostRegistry

namespace MachCSL.Logic.PlicWP
open Iris Iris.BI MachCSL.Machine

theorem registryPlicWPSpec [Platform] (invariants : Invariant.Names) :
    letI := UartGhost.nativeInvariant invariants
    PlicWPSpec UartGhost.machineCapacity := by
  letI := UartGhost.nativeInvariant invariants
  exact plicWPSpec UartGhost.machineCapacity

theorem registry_wp_plic_loop [Platform] (invariants : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (N : Namespace) (post : Empty → IProp UartGhost.registry) :
    letI := UartGhost.nativeInvariant invariants
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed generation era -∗
      wireInv UartGhost.machineCapacity.era.registers N era.registers -∗
      DeadThread.threadWP UartGhost.machineCapacity image fixed whole (.plic generation) post) := by
  letI := UartGhost.nativeInvariant invariants
  exact wp_plic_loop UartGhost.machineCapacity image fixed whole generation era N post

end MachCSL.Logic.PlicWP
