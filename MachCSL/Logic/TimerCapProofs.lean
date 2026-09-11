import MachCSL.Logic.TimerCapSpec
import MachCSL.Logic.RegisterProofs

namespace MachCSL.Logic.TimerCap
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance enabled_persistent era cpu : Persistent (enabled capacity era cpu) := by
  unfold enabled
  infer_instance

instance enabled_timeless era cpu : Timeless (enabled capacity era cpu) := by
  unfold enabled
  infer_instance

instance deadline_timeless era cpu : Timeless (deadline capacity era cpu) := by
  unfold deadline
  infer_instance

theorem deadline_intro era cpu value :
    iprop(Registers.regPointsto capacity (era.registers cpu) .stimecmp (.own 1) value ⊢
      deadline capacity era cpu) := by
  iintro H
  iunfold deadline
  iexists value
  iexact H

theorem enabled_intro era cpu dq value (tm : _get_Counteren_TM value = 1#1) :
    iprop(Registers.regPointsto capacity (era.registers cpu) .mcounteren dq value ⊢ |==>
      enabled capacity era cpu) := by
  iintro H
  imod Registers.regPointsto_persist capacity (era.registers cpu) .mcounteren dq value $$ H with H
  imodintro
  iunfold enabled
  iexists value
  iframe H
  ipureintro
  exact tm

theorem enabled_value era cpu dq value :
    iprop(⊢ enabled capacity era cpu -∗
      Registers.regPointsto capacity (era.registers cpu) .mcounteren dq value -∗
      ⌜_get_Counteren_TM value = 1#1⌝) := by
  iintro Hcap Hvalue
  iunfold enabled at Hcap
  icases Hcap with ⟨%stored, Hstored, %tm⟩
  ihave %same := Registers.regPointsto_agree capacity (era.registers cpu) .mcounteren
    .discard dq stored value $$ [Hstored Hvalue]
  · iframe Hstored Hvalue
  ipureintro
  exact same ▸ tm

variable {hlc : HasLC} [InvGS_gen hlc GF]

instance deadlineInv_persistent era cpu : Persistent (deadlineInv capacity era cpu) := by
  unfold deadlineInv
  infer_instance

instance capability_persistent era cpu : Persistent (capability capacity era cpu) := by
  unfold capability
  infer_instance

theorem capability_intro era cpu (E : CoPset) dq value limit
    (tm : _get_Counteren_TM value = 1#1) :
    iprop(⊢ Registers.regPointsto capacity (era.registers cpu) .mcounteren dq value -∗
      Registers.regPointsto capacity (era.registers cpu) .stimecmp (.own 1) limit ={E}=∗
      capability capacity era cpu) := by
  iintro Hcounter Hlimit
  imod enabled_intro capacity era cpu dq value tm $$ Hcounter with #Henabled
  imod inv_alloc timerN E (deadline capacity era cpu) $$ [Hlimit] with #Hinv
  · iintro !>
    iapply deadline_intro capacity era cpu limit $$ Hlimit
  imodintro
  unfold capability deadlineInv
  iframe Henabled Hinv

theorem actual : Spec capacity where
  deadline_intro := deadline_intro capacity
  enabled_intro := enabled_intro capacity
  capability_intro := capability_intro capacity
  enabled_value := enabled_value capacity

end MachCSL.Logic.TimerCap
