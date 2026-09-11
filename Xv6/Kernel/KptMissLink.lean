import Xv6.Kernel.KptMissProofs

namespace Xv6.Kernel.KptMiss
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem nativePureSpec : PureSpec := ⟨program_factor, after_update, fill_variant, coherent_after⟩

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := ⟨wp_miss capacity⟩

end Xv6.Kernel.KptMiss
