import MachCSL.Machine.SpinlockImageProofs
import MachCSL.Memory.Proofs

namespace MachCSL.Machine.SpinlockCodeIntegrity
open MachCSL.Memory

/-- No message in this era writes any of the actual instruction bytes. -/
def CodeUnwritten (log : WriteLog 64) : Prop :=
  ∀ message, message ∈ log → ∀ i : Fin 17, ∀ j, j < 4 →
    message.bytes (addressAdd (SpinlockImage.instructionAddress i) j) = none

end MachCSL.Machine.SpinlockCodeIntegrity
