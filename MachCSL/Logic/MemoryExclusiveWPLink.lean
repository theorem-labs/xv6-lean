import MachCSL.Logic.MemoryExclusiveWPProofs
import MachCSL.Logic.UartGhostRegistry

namespace MachCSL.Logic.MemoryExclusiveWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- Complete implementation at the existing shared 23-slot registry. -/
theorem registryMemoryExclusiveWPSpec [Platform] (names : Invariant.Names) :
    letI := UartGhost.nativeInvariant names
    MemoryExclusiveWPSpec UartGhost.machineCapacity := by
  letI := UartGhost.nativeInvariant names
  exact memoryExclusiveWPSpec UartGhost.machineCapacity

theorem registry_wp_exclusive [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (rr : Option Reservation) (post : Empty → IProp UartGhost.registry)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true) :
    letI := UartGhost.nativeInvariant names
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed gen era -∗
      Reservations.resvFrag UartGhost.machineCapacity.era.reservations era.reservations cpu rr -∗
      exclusivePremise UartGhost.machineCapacity image fixed whole gen era cpu n req k post -∗
      threadWP UartGhost.machineCapacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  letI := UartGhost.nativeInvariant names
  exact (registryMemoryExclusiveWPSpec names).exclusive image fixed whole gen era cpu n req k rr post ram exclusive

theorem registry_wp_bytes [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (rr : Option Reservation) (dq : DFrac)
    (word : BitVec (8 * n)) (post : Empty → IProp UartGhost.registry)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true) :
    letI := UartGhost.nativeInvariant names
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed gen era -∗
      Reservations.resvFrag UartGhost.machineCapacity.era.reservations era.reservations cpu rr -∗
      TsoRead.byteWindow UartGhost.machineCapacity.era.heap.ledger era.heap req.pa n dq word -∗
      ▷ (∀ view, TsoRead.byteWindow UartGhost.machineCapacity.era.heap.ledger era.heap req.pa n dq word -∗
        Reservations.resvFrag UartGhost.machineCapacity.era.reservations era.reservations cpu (some (snapshot req.pa n word)) -∗
        Tso.Views.viewLB UartGhost.machineCapacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP UartGhost.machineCapacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      threadWP UartGhost.machineCapacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  letI := UartGhost.nativeInvariant names
  exact (registryMemoryExclusiveWPSpec names).bytes image fixed whole gen era cpu n req k rr dq word post ram exclusive

end MachCSL.Logic.MemoryExclusiveWP
