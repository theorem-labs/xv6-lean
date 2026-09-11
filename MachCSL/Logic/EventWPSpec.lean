import MachCSL.Logic.EventWPDefs
import MachCSL.Logic.RegisterWPSpec
import MachCSL.Logic.MemoryReadWPSpec

namespace MachCSL.Logic.EventWP
open Iris Iris.BI MachCSL.Machine

structure EventWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  initialSplit : ∀ γ rs,
    iprop(Registers.initialCells capacity.era.registers γ rs ⊣⊢
      ownedCells capacity.era.registers γ rs ∗
      Registers.regPointsto capacity.era.registers γ .sig_seip (.own 1) (rs .sig_seip) ∗
      Registers.regPointsto capacity.era.registers γ .sig_meip (.own 1) (rs .sig_meip))
  fold : ∀ reads dq resources era (_access : RamAccess capacity era reads dq resources)
      image fixed whole generation cpu rs (program : SailM Unit) Q post,
    ExecPlan reads rs program Q →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      ownedCells capacity.era.registers (era.registers cpu) rs -∗ resources -∗
      (∀ result, ⌜Q () result⌝ -∗
        ownedCells capacity.era.registers (era.registers cpu) result -∗ resources -∗
        RegisterWP.threadWP capacity image fixed whole (.hart generation cpu (.pure ())) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart generation cpu program) post)

end MachCSL.Logic.EventWP
