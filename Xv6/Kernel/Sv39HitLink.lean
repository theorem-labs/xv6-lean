import Xv6.Kernel.Sv39HitProofs

namespace Xv6.Kernel.Sv39Hit
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem nativeFactorSpec : FactorSpec :=
  ⟨raw_factor, entry_update, kernel_head, denied, enabled_remainder,
    disabled_remainder, write_false, write_error, coherent_resume⟩

theorem nativePlanSpec : PlanSpec := ⟨head_plan, resume_plan⟩

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity :=
  ⟨wp_head capacity, wp_resume capacity⟩

end Xv6.Kernel.Sv39Hit
