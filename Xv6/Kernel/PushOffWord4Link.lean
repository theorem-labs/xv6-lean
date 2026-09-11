import Xv6.Kernel.PushOffWord4Proofs
namespace Xv6.Kernel.PushOffWord4
open Iris MachCSL.Machine MachCSL.Logic

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := ⟨wp_body capacity⟩
end Xv6.Kernel.PushOffWord4
