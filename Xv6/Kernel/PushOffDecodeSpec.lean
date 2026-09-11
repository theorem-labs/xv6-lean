import Xv6.Kernel.PushOffDecodeDefs

namespace Xv6.Kernel.PushOffDecode
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- Semantic certificates of actual generated calls and compressed
redirection, without fetching or executing the normalized instruction body. -/
structure Spec [Platform] : Prop where
  unique : ∀ shares i, RegisterFootprint.Unique (footprint shares i)
  source_config : ∀ i rs,
    rs .misa = 0x800000000014112d#64 → rs .cur_privilege = .Supervisor →
    rs .menvcfg = 0xa000000000000000#64 → Config i rs
  decode : ∀ shares i rs, Config i rs →
    RegisterPlan.Returns (footprint shares i) rs (program i) (PushOffCode.decoded i) rs
  compressed_expansion : ∀ i, PushOffCode.compressed i = true →
    execute (PushOffCode.decoded i) = (pure (.ExecuteAs (PushOffCode.normalized i)) : SailM ExecutionResult)
  compressed_plan : ∀ fp i rs, PushOffCode.compressed i = true →
    RegisterPlan.Returns fp rs (execute (PushOffCode.decoded i)) (.ExecuteAs (PushOffCode.normalized i)) rs
  base_normalized : ∀ i, PushOffCode.compressed i = false → PushOffCode.decoded i = PushOffCode.normalized i

end Xv6.Kernel.PushOffDecode
