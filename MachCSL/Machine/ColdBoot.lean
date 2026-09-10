import MachCSL.Machine.RegisterRun
import MachCSL.Machine.Platform

/-! A concrete non-vacuity witness for the real generated boot chain. The
machine's boot predicate still permits arbitrary initial register files; this
particular all-default file supplies one witness and does not narrow that model.
All computation below is checked by Lean's kernel, without native decision axioms. -/
namespace MachCSL.Machine

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def zeroRegisters (r : Register) : RegisterType r := by
  cases r <;> exact default

def bootResult (vector hart : BitVec 64) : Option (Unit × RegisterFile) :=
  registerRun 10000 (bootProgram vector hart pmaBoot) zeroRegisters

theorem boot_succeeds (vector hart : BitVec 64) : (bootResult vector hart).isSome = true := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

def bootRegisters (vector hart : BitVec 64) : RegisterFile :=
  ((bootResult vector hart).get (boot_succeeds vector hart)).2

private theorem unitPair_result {α : Type} (o : Option (Unit × α))
    (h : o.isSome = true) : o = some ((), (o.get h).2) := by
  cases o with
  | none => simp at h
  | some p => cases p with | mk u x => cases u; rfl

theorem bootResult_eq (vector hart : BitVec 64) :
    bootResult vector hart = some ((), bootRegisters vector hart) := by
  exact unitPair_result (bootResult vector hart) (boot_succeeds vector hart)

/-- A completed run exists for every reset vector and hart ID, under any bus,
with unchanged RAM and devices. The run performs only actual register events. -/
theorem boot_run (bus : Bus Device) (vector hart : BitVec 64)
    (memory : Memory.ByteMap 64) (devices : Device) :
    Run bus (bootProgram vector hart pmaBoot) ⟨zeroRegisters, memory, devices⟩ ()
      ⟨bootRegisters vector hart, memory, devices⟩ :=
  registerRun_sound bus 10000 _ _ _ () memory devices (bootResult_eq vector hart)

end MachCSL.Machine
