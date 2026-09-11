import MachCSL.Logic.PlicWPDefs

namespace MachCSL.Logic.PlicWP
open Iris Iris.BI MachCSL.Machine

structure PlicWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  allocate : ∀ names N E seip meip,
    iprop(⊢ wireCells capacity.era.registers names seip meip ={E}=∗ wireInv capacity.era.registers N names)
  loop : ∀ image fixed whole generation era N post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      wireInv capacity.era.registers N era.registers -∗
      DeadThread.threadWP capacity image fixed whole (.plic generation) post)

end MachCSL.Logic.PlicWP
