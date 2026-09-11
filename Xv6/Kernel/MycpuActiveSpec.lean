import Xv6.Kernel.MycpuActiveDefs

namespace Xv6.Kernel.MycpuActive
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

/-- No field assumes or claims safety of the actual execution body. -/
structure Spec [Platform] : Prop where
  factor : ∀ stepNo, run_hart_active stepNo =
    (PreSail.readReg .cur_privilege >>= fun privilege =>
      dispatchInterrupt privilege >>= fun pending => match pending with
      | some (intr, priv) => pure (.Step_Pending_Interrupt (intr, priv))
      | none => fetch () >>= afterFetch stepNo)
  dispatch : ∀ shares rs, rs .cur_privilege = .Supervisor → SupervisorInterrupt.Disabled rs →
    RegisterPlan.Returns (footprint shares) rs (PreSail.readReg .cur_privilege >>= dispatchInterrupt) none rs
  prepare : ∀ shares rs i region stepNo, Config rs i region →
    Prefix (footprint shares) rs (afterFetch stepNo (MycpuFetch.result i)) (executeTail i) (prepared i rs)

end Xv6.Kernel.MycpuActive
