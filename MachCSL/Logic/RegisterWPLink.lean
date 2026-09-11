import MachCSL.Logic.RegisterWPProofs
import MachCSL.Logic.InvariantLink

namespace MachCSL.Logic.RegisterWP
open Iris Iris.BI MachCSL.Machine

/-- Concrete implementation at the final twenty-slot registry; no callee-spec premises. -/
theorem registryRegisterWPSpec [Platform] (names : Invariant.Names) :
    letI := names.native Invariant.registryCapacity
    RegisterWPSpec Invariant.machineCapacity := by
  letI := names.native Invariant.registryCapacity
  exact registerWPSpec Invariant.machineCapacity

theorem registry_wp_read [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (r : Register) (dq : DFrac)
    (value : RegisterType r) (k : RegisterType r → SailM Unit) (post : Empty → IProp Invariant.registry) :
    letI := names.native Invariant.registryCapacity
    iprop(⊢ MachineInterp.generationCertificate Invariant.machineCapacity fixed generation era -∗
      Registers.regPointsto Invariant.machineCapacity.era.registers (era.registers cpu) r dq value -∗
      ▷ (Registers.regPointsto Invariant.machineCapacity.era.registers (era.registers cpu) r dq value -∗
        threadWP Invariant.machineCapacity image fixed whole (.hart generation cpu (k value)) post) -∗
      threadWP Invariant.machineCapacity image fixed whole (.hart generation cpu (.impure (.readReg r) k)) post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_read Invariant.machineCapacity image fixed whole generation era cpu r dq value k post

theorem registry_wp_write [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (r : Register)
    (old value : RegisterType r) (k : Unit → SailM Unit) (post : Empty → IProp Invariant.registry) :
    letI := names.native Invariant.registryCapacity
    iprop(⊢ MachineInterp.generationCertificate Invariant.machineCapacity fixed generation era -∗
      Registers.regPointsto Invariant.machineCapacity.era.registers (era.registers cpu) r (.own 1) old -∗
      ▷ (Registers.regPointsto Invariant.machineCapacity.era.registers (era.registers cpu) r (.own 1) value -∗
        threadWP Invariant.machineCapacity image fixed whole (.hart generation cpu (k ())) post) -∗
      threadWP Invariant.machineCapacity image fixed whole (.hart generation cpu (.impure (.writeReg r value) k)) post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_write Invariant.machineCapacity image fixed whole generation era cpu r old value k post

theorem registry_wp_read_any [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (cpu : CPU) (r : Register) (k : RegisterType r → SailM Unit) (post : Empty → IProp Invariant.registry) :
    letI := names.native Invariant.registryCapacity
    iprop(⊢ MachineInterp.generationCertificate Invariant.machineCapacity fixed generation era -∗
      ▷ (∀ value : RegisterType r,
        threadWP Invariant.machineCapacity image fixed whole (.hart generation cpu (k value)) post) -∗
      threadWP Invariant.machineCapacity image fixed whole (.hart generation cpu (.impure (.readReg r) k)) post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_read_any Invariant.machineCapacity image fixed whole generation era cpu r k post

end MachCSL.Logic.RegisterWP
