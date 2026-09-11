import MachCSL.Logic.RegisterWPDefs

namespace MachCSL.Logic.RegisterWP
open Iris Iris.BI MachCSL.Machine
structure RegisterWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  read : ∀ image fixed whole generation era cpu r dq (value : RegisterType r)
      (k : RegisterType r → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      Registers.regPointsto capacity.era.registers (era.registers cpu) r dq value -∗
      ▷ (Registers.regPointsto capacity.era.registers (era.registers cpu) r dq value -∗
        threadWP capacity image fixed whole (.hart generation cpu (k value)) post) -∗
      threadWP capacity image fixed whole (.hart generation cpu (.impure (.readReg r) k)) post)
  write : ∀ image fixed whole generation era cpu r (old value : RegisterType r)
      (k : Unit → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      Registers.regPointsto capacity.era.registers (era.registers cpu) r (.own 1) old -∗
      ▷ (Registers.regPointsto capacity.era.registers (era.registers cpu) r (.own 1) value -∗
        threadWP capacity image fixed whole (.hart generation cpu (k ())) post) -∗
      threadWP capacity image fixed whole (.hart generation cpu (.impure (.writeReg r value) k)) post)
  readAny : ∀ image fixed whole generation era cpu r (k : RegisterType r → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      ▷ (∀ value : RegisterType r,
        threadWP capacity image fixed whole (.hart generation cpu (k value)) post) -∗
      threadWP capacity image fixed whole (.hart generation cpu (.impure (.readReg r) k)) post)
end MachCSL.Logic.RegisterWP
