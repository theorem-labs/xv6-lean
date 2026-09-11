import MachCSL.Machine.JalLoopDefs

namespace MachCSL.Machine.JalLoop

theorem override_dynamic (base : RegisterFile) : override base (dynamic base) = base := by
  funext r
  cases r <;> rfl

theorem boot_canonical (cpu : CPU) :
    Canonical cpu (bootRegisters jalImage.vector (BitVec.ofNat 64 cpu.val)) :=
  ⟨dynamic _, (override_dynamic _).symm⟩

theorem override_write_supervisor (base : RegisterFile) (d : Dynamic) (value : BitVec 1) :
    Sail.Registers.write (override base d) .sig_seip value =
      override base { d with supervisor := value } := by
  funext r
  cases r <;> rfl

theorem override_write_machine (base : RegisterFile) (d : Dynamic) (value : BitVec 1) :
    Sail.Registers.write (override base d) .sig_meip value =
      override base { d with machine := value } := by
  funext r
  cases r <;> rfl

theorem write_supervisor (cpu : CPU) (d : Dynamic) (value : BitVec 1) :
    Sail.Registers.write (registers cpu d) .sig_seip value =
      registers cpu { d with supervisor := value } := override_write_supervisor _ d value

theorem write_machine (cpu : CPU) (d : Dynamic) (value : BitVec 1) :
    Sail.Registers.write (registers cpu d) .sig_meip value =
      registers cpu { d with machine := value } := override_write_machine _ d value

theorem canonical_write_supervisor (cpu : CPU) (rs : RegisterFile) (value : BitVec 1)
    (canonical : Canonical cpu rs) : Canonical cpu (Sail.Registers.write rs .sig_seip value) := by
  obtain ⟨d, rfl⟩ := canonical
  exact ⟨{ d with supervisor := value }, write_supervisor cpu d value⟩

theorem canonical_write_machine (cpu : CPU) (rs : RegisterFile) (value : BitVec 1)
    (canonical : Canonical cpu rs) : Canonical cpu (Sail.Registers.write rs .sig_meip value) := by
  obtain ⟨d, rfl⟩ := canonical
  exact ⟨{ d with machine := value }, write_machine cpu d value⟩

theorem plic_preserves (devices : Devices.State) (rs rs' : CPU → RegisterFile)
    (canonical : AllCanonical rs) (step : PlicStep devices rs rs') : AllCanonical rs' := by
  cases step with
  | supervisor cpu =>
    intro other
    by_cases h : other = cpu
    · subst other
      simp only [updateHart, ↓reduceIte]
      exact canonical_write_supervisor cpu (rs cpu) _ (canonical cpu)
    · simpa [updateHart, h] using canonical other
  | machine cpu =>
    intro other
    by_cases h : other = cpu
    · subst other
      simp only [updateHart, ↓reduceIte]
      exact canonical_write_machine cpu (rs cpu) _ (canonical cpu)
    · simpa [updateHart, h] using canonical other

end MachCSL.Machine.JalLoop
