import MachCSL.Logic.EraSpec
import MachCSL.Logic.StateInterpSpec

namespace MachCSL.Logic.EraState
open MachCSL.Machine

def withRegisters (g : State) (files : CPU → RegisterFile) : State := { g with registers := files }

def writeRegister (g : State) (cpu : CPU) (r : Register) (value : RegisterType r) : State :=
  withRegisters g (updateHart g.registers cpu (Sail.Registers.write (g.registers cpu) r value))

end MachCSL.Logic.EraState
