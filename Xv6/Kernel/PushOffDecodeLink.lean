import Xv6.Kernel.PushOffDecodeProofs

namespace Xv6.Kernel.PushOffDecode
open MachCSL.Machine

/-- All source AST rows are now tied to actual generated decoder plans and
compressed execution. No caller snapshot/certificate/component premise. -/
theorem nativeSpec [Platform] : Spec where
  unique := unique
  source_config := source_config
  decode := decode
  compressed_expansion := compressed_expansion
  compressed_plan := compressed_plan
  base_normalized := base_normalized

end Xv6.Kernel.PushOffDecode
