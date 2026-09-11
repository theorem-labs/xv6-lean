import MachCSL.Logic.BarrierWPProofs
import MachCSL.Logic.UartGhostRegistry

namespace MachCSL.Logic.BarrierWP
open Iris Iris.BI MachCSL.Machine

/-- Existing shared 23-slot machine capacity and its supplied native invariant
names. No camera or second invariant world is allocated by this link. -/
theorem registryBarrierWPSpec [Platform] (names : Invariant.Names) :
    letI := UartGhost.nativeInvariant names
    BarrierWPSpec UartGhost.machineCapacity := by
  letI := UartGhost.nativeInvariant names
  exact barrierWPSpec UartGhost.machineCapacity

theorem registry_wp_ghost [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (kind : barrier_kind)
    (k : Unit → SailM Unit) (P Q : IProp UartGhost.registry) (post : Empty → IProp UartGhost.registry) :
    letI := UartGhost.nativeInvariant names
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed gen era -∗
      ghostStep UartGhost.machineCapacity.era era P Q -∗ P -∗
      ▷ (Q -∗ threadWP UartGhost.machineCapacity image fixed whole (.hart gen cpu (k ())) post) -∗
      threadWP UartGhost.machineCapacity image fixed whole (.hart gen cpu (.impure (.barrier kind) k)) post) := by
  letI := UartGhost.nativeInvariant names
  exact (registryBarrierWPSpec names).ghost image fixed whole gen era cpu kind k P Q post

theorem registry_wp_publish [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (kind : barrier_kind)
    (k : Unit → SailM Unit) (P Q : IProp UartGhost.registry) (post : Empty → IProp UartGhost.registry)
    (drains : fenceDrains kind = true) :
    letI := UartGhost.nativeInvariant names
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed gen era -∗
      pubStep UartGhost.machineCapacity.era era cpu P Q -∗ P -∗
      ▷ (Q -∗ threadWP UartGhost.machineCapacity image fixed whole (.hart gen cpu (k ())) post) -∗
      threadWP UartGhost.machineCapacity image fixed whole (.hart gen cpu (.impure (.barrier kind) k)) post) := by
  letI := UartGhost.nativeInvariant names
  exact (registryBarrierWPSpec names).publish image fixed whole gen era cpu kind k P Q post drains

theorem registry_wp_identity [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (kind : barrier_kind)
    (k : Unit → SailM Unit) (post : Empty → IProp UartGhost.registry) :
    letI := UartGhost.nativeInvariant names
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed gen era -∗
      ▷ threadWP UartGhost.machineCapacity image fixed whole (.hart gen cpu (k ())) post -∗
      threadWP UartGhost.machineCapacity image fixed whole (.hart gen cpu (.impure (.barrier kind) k)) post) := by
  letI := UartGhost.nativeInvariant names
  exact wp_identity UartGhost.machineCapacity image fixed whole gen era cpu kind k post

end MachCSL.Logic.BarrierWP
