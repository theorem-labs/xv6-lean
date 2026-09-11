import MachCSL.Machine.SpinlockPoolSpec

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan

/-- Reindex the very same exclusive-read residual after its actual blocked
arm clears the reservation. No successful continuation depends on incoming rr. -/
theorem blocked_exclusive_plan {S α : Type} {reads : EventWP.ReadAllowed} {rel : Relations S}
    {rs rr s n} {req : ReadRequest n} {k : MemoryReadWP.ReadResult n → SailM α}
    {Q : α → RegisterFile → Option Reservation → S → Prop}
    (plan : Plan reads rel rs rr s (.impure (.readMem n req) k) Q)
    (exclusive : accessExclusive req.access_kind = true) :
    Plan reads rel rs none s (.impure (.readMem n req) k) Q := by
  cases EventPlanHead.head_of_plan plan with
  | codeRead ram plain allowed rest => simp [plain] at exclusive
  | plain enabled ram kind rest => simp [kind] at exclusive
  | exclusive enabled ram kind rest => exact .exclusive enabled ram kind rest

end MachCSL.Machine.SpinlockPool
