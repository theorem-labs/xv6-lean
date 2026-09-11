import MachCSL.Machine.JalLoopBootFacts

/-! Actual generated interrupt dispatch with arbitrary pending bits and external
pins. Machine-mode global interrupt disable is inherited from real boot. -/
namespace MachCSL.Machine.JalLoop
open LeanPaperStock.Functions

private def dispatchStatic (base : RegisterFile) (r : Register) : RegisterType r :=
  match r with
  | .misa => 0x800000000014112d#64
  | .mstatus => 0xA00000000#64
  | .mie => 0#64
  | .mideleg => 0#64
  | other => base other

private theorem dispatchStatic_eq (base : RegisterFile)
    (misa : base .misa = 0x800000000014112d#64)
    (status : base .mstatus = 0xA00000000#64)
    (ie : base .mie = 0#64) (delegation : base .mideleg = 0#64) :
    dispatchStatic base = base := by
  funext r
  cases r <;> simp only [dispatchStatic, misa, status, ie, delegation]

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

private theorem dispatch_static [Platform] (base : RegisterFile) :
    registerRun 100 (dispatchInterrupt .Machine) (dispatchStatic base) =
      some (none, dispatchStatic base) := by cbv

theorem dispatch_registers [Platform] (cpu : CPU) (d : Dynamic) :
    registerRun 100 (dispatchInterrupt .Machine) (registers cpu d) =
      some (none, registers cpu d) := by
  have h := boot_static (BitVec.ofNat 64 cpu.val)
  simp only [Prod.mk.injEq] at h
  have same : dispatchStatic (registers cpu d) = registers cpu d := by
    apply dispatchStatic_eq
    · exact bootRegisters_misa jalImage.vector (BitVec.ofNat 64 cpu.val)
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
  simpa only [same] using dispatch_static (registers cpu d)

end MachCSL.Machine.JalLoop
