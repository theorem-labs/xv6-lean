import MachCSL.Logic.MemoryReadWPProofs
import MachCSL.Logic.InvariantLink

namespace MachCSL.Logic.MemoryReadWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- All conditional and concrete read rules at the same final machine registry. -/
theorem registryMemoryReadWPSpec [Platform] (names : Invariant.Names) :
    letI := names.native Invariant.registryCapacity
    MemoryReadWPSpec Invariant.machineCapacity := by
  letI := names.native Invariant.registryCapacity
  exact memoryReadWPSpec Invariant.machineCapacity

theorem registry_wp_ram_read_plain_ex [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (P : BitVec (8 * n) → Prop) (post : Empty → IProp Invariant.registry)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    letI := names.native Invariant.registryCapacity
    iprop(⊢ MachineInterp.generationCertificate Invariant.machineCapacity fixed gen era -∗
      plainPremise Invariant.machineCapacity image fixed whole gen era cpu n req k P post -∗
      threadWP Invariant.machineCapacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_ram_read_plain_ex Invariant.machineCapacity image fixed whole gen era cpu n req k P post ram plain

theorem registry_wp_ram_read_plain [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (post : Empty → IProp Invariant.registry)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    letI := names.native Invariant.registryCapacity
    iprop(⊢ MachineInterp.generationCertificate Invariant.machineCapacity fixed gen era -∗
      plainWordPremise Invariant.machineCapacity image fixed whole gen era cpu n req k post -∗
      threadWP Invariant.machineCapacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_ram_read_plain Invariant.machineCapacity image fixed whole gen era cpu n req k post ram plain

theorem registry_wp_ram_read_pristine [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (dq : DFrac) (word : BitVec (8 * n)) (post : Empty → IProp Invariant.registry)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    letI := names.native Invariant.registryCapacity
    iprop(⊢ MachineInterp.generationCertificate Invariant.machineCapacity fixed gen era -∗
      TsoRead.byteWindow Invariant.machineCapacity.era.heap.ledger era.heap req.pa n dq word -∗
      TsoRead.pristineWindow Invariant.machineCapacity.era.heap.ledger era.timestamps req.pa n -∗
      ▷ (∀ view, TsoRead.byteWindow Invariant.machineCapacity.era.heap.ledger era.heap req.pa n dq word -∗
        Tso.Views.viewLB Invariant.machineCapacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP Invariant.machineCapacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      threadWP Invariant.machineCapacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_ram_read_pristine Invariant.machineCapacity image fixed whole gen era cpu n req k dq word post ram plain

theorem registry_wp_ram_read_pristine_mint [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat) (req : ReadRequest n)
    (k : ReadResult n → SailM Unit) (dq : DFrac) (word : BitVec (8 * n)) (post : Empty → IProp Invariant.registry)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    letI := names.native Invariant.registryCapacity
    iprop(⊢ MachineInterp.generationCertificate Invariant.machineCapacity fixed gen era -∗
      TsoRead.byteWindow Invariant.machineCapacity.era.heap.ledger era.heap req.pa n dq word -∗
      TsoRead.initialTimestampWindow Invariant.machineCapacity.era.heap.ledger era.timestamps req.pa n -∗
      ▷ (∀ view, TsoRead.byteWindow Invariant.machineCapacity.era.heap.ledger era.heap req.pa n dq word -∗
        TsoRead.pristineWindow Invariant.machineCapacity.era.heap.ledger era.timestamps req.pa n -∗
        Tso.Views.viewLB Invariant.machineCapacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP Invariant.machineCapacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      threadWP Invariant.machineCapacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_ram_read_pristine_mint Invariant.machineCapacity image fixed whole gen era cpu n req k dq word post ram plain

end MachCSL.Logic.MemoryReadWP
