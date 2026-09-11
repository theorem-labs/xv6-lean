import MachCSL.Logic.TimerCapDefs

namespace MachCSL.Logic.TimerCap
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  deadline_intro : ∀ era cpu value,
    iprop(Registers.regPointsto capacity (era.registers cpu) .stimecmp (.own 1) value ⊢
      deadline capacity era cpu)
  enabled_intro : ∀ era cpu dq value, _get_Counteren_TM value = 1#1 →
    iprop(Registers.regPointsto capacity (era.registers cpu) .mcounteren dq value ⊢ |==>
      enabled capacity era cpu)
  capability_intro : ∀ era cpu (E : CoPset) dq value limit, _get_Counteren_TM value = 1#1 →
    iprop(⊢ Registers.regPointsto capacity (era.registers cpu) .mcounteren dq value -∗
      Registers.regPointsto capacity (era.registers cpu) .stimecmp (.own 1) limit ={E}=∗
      capability capacity era cpu)
  enabled_value : ∀ era cpu dq value,
    iprop(⊢ enabled capacity era cpu -∗
      Registers.regPointsto capacity (era.registers cpu) .mcounteren dq value -∗
      ⌜_get_Counteren_TM value = 1#1⌝)

end MachCSL.Logic.TimerCap
