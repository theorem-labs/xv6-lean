import MachCSL.Machine.SpinlockCoreDefs
import MachCSL.Machine.SpinlockCycleDefs
import MachCSL.Machine.SpinlockScalarDefs
import MachCSL.Machine.SpinlockControlDefs

namespace MachCSL.Machine.SpinlockCore

theorem write {cpu : CPU} {rs : RegisterFile} (core : Core cpu rs) {r : Register}
    (value : RegisterType r) (allowed : Writable r) : Core cpu (Sail.Registers.write rs r value) := by
  cases r <;> simp only [Writable] at allowed
  all_goals first | contradiction | skip
  all_goals exact ⟨⟨core.misa, core.mstatus, core.menvcfg, core.mseccfg, core.privilege, core.pma, core.htif⟩,
    core.mie, core.mideleg, core.elp, core.hartState, core.off, core.hartid⟩

theorem atInstruction {cpu rs} (core : Core cpu rs) (i : Fin 17)
    (pc : rs .PC = SpinlockImage.instructionAddress i)
    (next : rs .nextPC = SpinlockImage.instructionAddress i) : SpinlockFetch.Static i rs :=
  ⟨pc, next, core.misa, core.mstatus, core.mie, core.mideleg, core.menvcfg,
    core.elp, core.mseccfg, core.privilege, core.hartState, core.pma, core.htif⟩

theorem boot (image : BootImage) (g : State) (facts : BootFacts image g) (cpu : CPU) :
    Core cpu (g.registers cpu) := by
  have static := BootUniversal.bootFacts_static image g facts cpu
  exact ⟨⟨static.misa, static.mstatus, static.menvcfg, static.mseccfg, static.privilege, static.pma, static.htif⟩,
    static.mie, static.mideleg, static.elp, static.hartState,
    BootPmp.bootFacts_off image g facts cpu, BootHartId.bootFacts_hartid image g facts cpu⟩

theorem enable {cpu rs} (core : Core cpu rs) : Core cpu (JalLoopPlan.enableAfter rs) :=
  write core _ trivial

theorem prepare {cpu rs} (core : Core cpu rs) : Core cpu (SpinlockCycle.prepare rs) :=
  write core _ trivial

theorem tickPC {cpu rs} (core : Core cpu rs) : Core cpu (SpinlockCycle.tickPC rs) :=
  write core _ trivial

theorem retire {cpu rs} (core : Core cpu rs) : Core cpu (SpinlockCycle.retire rs) := by
  unfold SpinlockCycle.retire
  split
  · exact write core _ trivial
  · exact core

theorem clock {cpu rs} (core : Core cpu rs) : Core cpu (JalLoopPlan.clockAfter rs) := by
  unfold JalLoopPlan.clockAfter JalLoopPlan.timeAfter JalLoopPlan.counterAfter JalLoop.clintAfter
  split
  · exact write (r := .mip) (write (r := .mtime) (write (r := .mcycle) core _ trivial) _ trivial) _ trivial
  · exact write (r := .mip) (write (r := .mtime) core _ trivial) _ trivial

theorem finish {cpu rs} (core : Core cpu rs) (tick : Bool) : Core cpu (SpinlockCycle.finish tick rs) := by
  cases tick
  · exact retire (tickPC core)
  · exact clock (retire (tickPC core))

theorem scalar {cpu rs} (core : Core cpu rs) (i : Fin 7) : Core cpu (SpinlockScalar.after i rs) := by
  unfold SpinlockScalar.after
  split <;> exact write core _ trivial

theorem csr {cpu rs} (core : Core cpu rs) : Core cpu (SpinlockControl.csrAfter rs) :=
  write core _ trivial

theorem branch {cpu rs} (core : Core cpu rs) (retry : Bool) : Core cpu (SpinlockControl.branchAfter retry rs) := by
  unfold SpinlockControl.branchAfter
  cases retry
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals split
  all_goals first | exact write (r := .nextPC) core _ trivial | exact core

theorem pin {cpu rs} (core : Core cpu rs) (r : Register) (isPin : Logic.EventWP.IsPin r)
    (value : RegisterType r) : Core cpu (Sail.Registers.write rs r value) := by
  rcases isPin with rfl | rfl
  all_goals exact write core value trivial

theorem plic (devices : Devices.State) (before after : CPU → RegisterFile)
    (cores : ∀ cpu, Core cpu (before cpu)) (step : PlicStep devices before after) :
    ∀ cpu, Core cpu (after cpu) := by
  cases step with
  | supervisor selected =>
    intro cpu
    by_cases same : cpu = selected
    · subst cpu
      simp only [updateHart, ite_true]
      exact pin (cores selected) .sig_seip (Or.inl rfl) _
    · simpa only [updateHart, if_neg same] using cores cpu
  | machine selected =>
    intro cpu
    by_cases same : cpu = selected
    · subst cpu
      simp only [updateHart, ite_true]
      exact pin (cores selected) .sig_meip (Or.inr rfl) _
    · simpa only [updateHart, if_neg same] using cores cpu

private theorem retire_pc_pair (rs : RegisterFile) :
    ((SpinlockCycle.retire rs) .PC, (SpinlockCycle.retire rs) .nextPC) = (rs .PC, rs .nextPC) := by
  unfold SpinlockCycle.retire
  split <;> rfl

private theorem clock_pc_pair (rs : RegisterFile) :
    ((JalLoopPlan.clockAfter rs) .PC, (JalLoopPlan.clockAfter rs) .nextPC) = (rs .PC, rs .nextPC) := by
  unfold JalLoopPlan.clockAfter JalLoopPlan.timeAfter JalLoopPlan.counterAfter JalLoop.clintAfter
  split <;> rfl

theorem finish_pc_pair (tick : Bool) (rs : RegisterFile) :
    ((SpinlockCycle.finish tick rs) .PC, (SpinlockCycle.finish tick rs) .nextPC) =
      (rs .nextPC, rs .nextPC) := by
  cases tick
  · exact retire_pc_pair (SpinlockCycle.tickPC rs)
  · exact (clock_pc_pair (SpinlockCycle.retire (SpinlockCycle.tickPC rs))).trans
      (retire_pc_pair (SpinlockCycle.tickPC rs))

theorem finish_pc (tick : Bool) (rs : RegisterFile) :
    (SpinlockCycle.finish tick rs) .PC = rs .nextPC := congrArg Prod.fst (finish_pc_pair tick rs)

theorem finish_nextPC (tick : Bool) (rs : RegisterFile) :
    (SpinlockCycle.finish tick rs) .nextPC = rs .nextPC := congrArg Prod.snd (finish_pc_pair tick rs)

theorem finish_atInstruction {cpu rs} (core : Core cpu rs) (tick : Bool) (i : Fin 17)
    (next : rs .nextPC = SpinlockImage.instructionAddress i) :
    SpinlockFetch.Static i (SpinlockCycle.finish tick rs) :=
  atInstruction (finish core tick) i ((finish_pc tick rs).trans next) ((finish_nextPC tick rs).trans next)

end MachCSL.Machine.SpinlockCore
