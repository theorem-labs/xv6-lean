import MachCSL.Logic.EraStateDefs

namespace MachCSL.Logic.EraState
open Iris Iris.BI MachCSL.Machine

structure EraStateSpec {GF : BundledGFunctors} (capacity : Era.Capacity GF) : Prop where
  registersAccess : ∀ era g,
    iprop(⊢ Era.interp capacity era g -∗
      GlobalRegisters.gregsInterp capacity.registers era.registers g.registers ∗
      (∀ files, GlobalRegisters.gregsInterp capacity.registers era.registers files -∗
        Era.interp capacity era (withRegisters g files)))
  read : GlobalRegisters.GlobalRegisterSpec capacity.registers → ∀ era g cpu r dq value,
    iprop(⊢ Era.interp capacity era g -∗
      Registers.regPointsto capacity.registers (era.registers cpu) r dq value -∗
      ⌜g.registers cpu r = value⌝)
  write : GlobalRegisters.GlobalRegisterSpec capacity.registers → ∀ era g cpu r old value,
    iprop(⊢ Era.interp capacity era g -∗
      Registers.regPointsto capacity.registers (era.registers cpu) r (.own 1) old ==∗
      Era.interp capacity era (writeRegister g cpu r value) ∗
      Registers.regPointsto capacity.registers (era.registers cpu) r (.own 1) value)

end MachCSL.Logic.EraState
