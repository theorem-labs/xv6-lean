import MachCSL.Logic.EraDefs
import Iris.Instances.Lib.Invariants
import LeanPaperStock.SysRegs

/-! Exact source TimerCap.v ownership. The per-hart counter enable is
persisted from an owned register; the deadline cell is kept in an invariant.
This is no execution theorem for timerinit or CSR instructions. -/
namespace MachCSL.Logic.TimerCap
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

abbrev Capacity := Registers.Capacity

def timerN : Namespace := nroot.@("timer" : String)

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record) (cpu : CPU)

def enabled : IProp GF :=
  iprop(∃ value : BitVec 32,
    Registers.regPointsto capacity (era.registers cpu) .mcounteren .discard value ∗
    ⌜_get_Counteren_TM value = 1#1⌝)

def deadline : IProp GF :=
  iprop(∃ value : BitVec 64,
    Registers.regPointsto capacity (era.registers cpu) .stimecmp (.own 1) value)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def deadlineInv : IProp GF := inv timerN (deadline capacity era cpu)

noncomputable def capability : IProp GF := iprop(enabled capacity era cpu ∗ deadlineInv capacity era cpu)

end MachCSL.Logic.TimerCap
