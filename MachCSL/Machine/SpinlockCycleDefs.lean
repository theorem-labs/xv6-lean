import MachCSL.Machine.SpinlockFetchProofs
import MachCSL.Machine.SpinlockDecodeProofs
import MachCSL.Logic.EventPlanCombinators

namespace MachCSL.Machine.SpinlockCycle
open LeanPaperStock.Functions

def prepare (rs : RegisterFile) : RegisterFile :=
  Sail.Registers.write rs .nextPC (Sail.BitVec.addInt (rs .PC) 4)

def tickPC (rs : RegisterFile) : RegisterFile :=
  Sail.Registers.write rs .PC (rs .nextPC)

def retire (rs : RegisterFile) : RegisterFile :=
  if rs .minstret_increment then
    Sail.Registers.write rs .minstret (Sail.BitVec.addInt (rs .minstret) 1)
  else rs

def finish (tick : Bool) (rs : RegisterFile) : RegisterFile :=
  if tick then JalLoopPlan.clockAfter (retire (tickPC rs)) else retire (tickPC rs)

end MachCSL.Machine.SpinlockCycle
