import Xv6.Kernel.MycpuBareWitnessRunProofs
namespace Xv6.Kernel.MycpuBareWitness
open MachCSL MachCSL.Machine MachCSL.Logic
attribute [local instance] platform
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Counter placement is irrelevant to every data register, uniformly in the
cycle index. The seven excluded control fields are checked separately when
turning this relation into full register-file equality. -/
theorem ordered_core (k : Nat) :
    MycpuBare.CoreEq
      (SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry k (checkpoint k))) (checkpoint (k+1)) := by
  have input := MycpuBare.CoreEq.write_ignored (MycpuBare.reference entry k) Register.minstret
    (BitVec.ofNat 64 k) (by decide)
  have body := MycpuBare.body_core entry k (MycpuBare.reference entry k) (checkpoint k) input
    (Sail.Registers.write_other (MycpuBare.reference entry k) Register.minstret Register.PC _ (by decide))
  have finish := MycpuBare.completed_core (MycpuBare.bodyFile entry k (checkpoint k))
    (SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry k (checkpoint k))) (fun _ _ => rfl)
  have expected : MycpuBare.CoreEq (MycpuBare.bodyFile entry k (MycpuBare.reference entry k))
      (checkpoint (k+1)) :=
    (MycpuBare.CoreEq.write_ignored _ Register.PC _ (by decide)).trans
      (MycpuBare.CoreEq.write_ignored _ Register.minstret _ (by decide))
  exact (body.trans finish).symm.trans expected

end Xv6.Kernel.MycpuBareWitness
