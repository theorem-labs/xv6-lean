import MachCSL.Machine.JalLoopUniversalFetch

/-! The exact relevant family available after every permitted JAL-image boot.
It constrains neither counter configuration nor PMP addresses/unrelated cfg bits. -/
namespace MachCSL.Machine.JalLoopPlan
open MachCSL.Logic.EventWP

def UniversalFamily (rs : RegisterFile) : Prop := Static rs ∧ BootPmp.Off rs

theorem off_enable (rs : RegisterFile) (off : BootPmp.Off rs) : BootPmp.Off (enableAfter rs) := off

theorem off_retire (rs : RegisterFile) (off : BootPmp.Off rs) : BootPmp.Off (retireAfter rs) := by
  unfold retireAfter
  split <;> exact off

theorem off_clock (rs : RegisterFile) (off : BootPmp.Off rs) : BootPmp.Off (clockAfter rs) := by
  unfold clockAfter timeAfter counterAfter
  split <;> exact off

theorem off_cycle (tick : Bool) (rs : RegisterFile) (off : BootPmp.Off rs) :
    BootPmp.Off (cycleAfter tick rs) := by
  cases tick
  · exact off_retire rs off
  · exact off_clock _ (off_retire rs off)

theorem universalFamily_cycle (tick : Bool) (rs : RegisterFile) (family : UniversalFamily rs) :
    UniversalFamily (cycleAfter tick rs) :=
  ⟨static_cycle tick rs family.1, off_cycle tick rs family.2⟩

theorem universal_cycle_plan [Platform] (tick : Bool) (rs : RegisterFile)
    (family : UniversalFamily rs) :
    Returns CodeRead rs (cycle tick) () (cycleAfter tick rs) :=
  cycle_plan CodeRead rs family.1 tick
    (universal_fetch_plan (enableAfter rs) (static_enable rs family.1) (off_enable rs family.2))

/-- The family holds for every actual nondeterministic boot witness, with no
zero-register prestate or canonical PMP-address assumption. -/
theorem bootFacts_family (g : State) (facts : BootFacts jalImage g) (cpu : CPU) :
    UniversalFamily (g.registers cpu) :=
  ⟨BootUniversal.bootFacts_static jalImage g facts cpu, BootPmp.bootFacts_off jalImage g facts cpu⟩

theorem family_pin (rs : RegisterFile) (family : UniversalFamily rs) (r : Register)
    (pin : IsPin r) (value : RegisterType r) : UniversalFamily (Sail.Registers.write rs r value) := by
  obtain ⟨static, off⟩ := family
  rcases pin with rfl | rfl
  all_goals
    exact ⟨⟨static.pc, static.nextPC, static.misa, static.mstatus, static.mie, static.mideleg,
      static.menvcfg, static.elp, static.mseccfg, static.privilege, static.hartState, static.pma, static.htif⟩, off⟩

theorem family_plic (devices : Devices.State) (before after : CPU → RegisterFile)
    (family : ∀ cpu, UniversalFamily (before cpu)) (step : PlicStep devices before after) :
    ∀ cpu, UniversalFamily (after cpu) := by
  cases step with
  | supervisor selected =>
    intro cpu
    by_cases same : cpu = selected
    · subst cpu
      simp only [updateHart, ite_true]
      exact family_pin _ (family selected) .sig_seip (Or.inl rfl) _
    · simpa only [updateHart, if_neg same] using family cpu
  | machine selected =>
    intro cpu
    by_cases same : cpu = selected
    · subst cpu
      simp only [updateHart, ite_true]
      exact family_pin _ (family selected) .sig_meip (Or.inr rfl) _
    · simpa only [updateHart, if_neg same] using family cpu

end MachCSL.Machine.JalLoopPlan
