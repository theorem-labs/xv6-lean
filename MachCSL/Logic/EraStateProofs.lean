import MachCSL.Logic.EraStateSpec

namespace MachCSL.Logic.EraState
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Era.Capacity GF)

theorem registers_access (era : Era.Record) (g : State) :
    iprop(⊢ Era.interp capacity era g -∗
      GlobalRegisters.gregsInterp capacity.registers era.registers g.registers ∗
      (∀ files, GlobalRegisters.gregsInterp capacity.registers era.registers files -∗
        Era.interp capacity era (withRegisters g files))) := by
  unfold Era.interp
  iintro ⟨Hregs, Hrest⟩
  isplitl [Hregs]
  · iexact Hregs
  · iintro %files Hregs
    have heap : Era.heapInterpAt capacity era (withRegisters g files) = Era.heapInterpAt capacity era g := rfl
    have tso : Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes (withRegisters g files) =
      Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes g := rfl
    have resv : ReservationsOK (withRegisters g files) = ReservationsOK g := rfl
    rw [heap, tso, resv]
    unfold withRegisters
    iframe Hregs
    iexact Hrest

theorem read_register (registers : GlobalRegisters.GlobalRegisterSpec capacity.registers)
    (era : Era.Record) (g : State) (cpu : CPU) (r : Register) (dq : DFrac) (value : RegisterType r) :
    iprop(⊢ Era.interp capacity era g -∗
      Registers.regPointsto capacity.registers (era.registers cpu) r dq value -∗
      ⌜g.registers cpu r = value⌝) := by
  unfold Era.interp
  iintro ⟨Hregs, _⟩ Hvalue
  iapply registers.read era.registers g.registers cpu r dq value $$ Hregs Hvalue

theorem write_register (registers : GlobalRegisters.GlobalRegisterSpec capacity.registers)
    (era : Era.Record) (g : State) (cpu : CPU) (r : Register) (old value : RegisterType r) :
    iprop(⊢ Era.interp capacity era g -∗
      Registers.regPointsto capacity.registers (era.registers cpu) r (.own 1) old ==∗
      Era.interp capacity era (writeRegister g cpu r value) ∗
      Registers.regPointsto capacity.registers (era.registers cpu) r (.own 1) value) := by
  iintro Hera Hvalue
  ihave ⟨Hregs, Hback⟩ := registers_access capacity era g $$ Hera
  imod registers.write era.registers g.registers cpu r old value $$ Hregs Hvalue with ⟨Hregs, Hvalue⟩
  imodintro
  iframe Hvalue
  unfold writeRegister
  iapply Hback $$ Hregs

theorem writeBack_register (g : State) (cpu : CPU) (r : Register) (value : RegisterType r) :
    writeBack g cpu { focus g cpu with registers := Sail.Registers.write (g.registers cpu) r value } =
      writeRegister g cpu r value := by
  have same {α : Type} (f : CPU → α) : updateHart f cpu (f cpu) = f := by
    funext other
    by_cases h : other = cpu <;> simp [updateHart, h]
  simp only [writeBack, focus, writeRegister, withRegisters, same]

theorem eraStateSpec : EraStateSpec capacity :=
  ⟨registers_access capacity, read_register capacity, write_register capacity⟩

end MachCSL.Logic.EraState
