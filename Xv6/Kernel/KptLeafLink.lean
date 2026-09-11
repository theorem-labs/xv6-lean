import Xv6.Kernel.KptLeafPlan

namespace Xv6.Kernel.KptLeaf

/-- Source kernel leaf layout, including arbitrary A/D bits and symbolic PPN. -/
theorem nativeWordSpec : WordSpec := wordSpec

/-- Actual generated permission/invalid/level-zero leaf programs, retaining
every eager register read through universal native register plans. -/
theorem nativePlanSpec : PlanSpec := planSpec

end Xv6.Kernel.KptLeaf
