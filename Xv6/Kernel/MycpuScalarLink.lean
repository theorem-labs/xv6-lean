import Xv6.Kernel.MycpuScalarSpec
import Xv6.Kernel.MycpuScalarProofs
import Xv6.Kernel.MycpuScalarGeometry

namespace Xv6.Kernel.MycpuScalar
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

/-- Native partial-footprint rule for the real scalar body, including compressed
redirection. The continuation remains the actual free-program continuation. -/
theorem wp_scalar {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) pcShare tpShare (i : Fin 9)
    image fixed whole gen era cpu rs (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs
        (footprint pcShare tpShare) -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (after i rs)
          (footprint pcShare tpShare) -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (body i >>= continuation)) post) := by
  iintro Hcert Hregs Hcontinue
  iapply RegisterPlan.fold capacity (footprint pcShare tpShare) (footprint_unique pcShare tpShare)
    image fixed whole gen era cpu rs (body i) _ continuation post
    (body_plan pcShare tpShare i rs) $$ Hcert Hregs
  iintro %value %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hcontinue $$ Hregs

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := ⟨wp_scalar capacity⟩

end Xv6.Kernel.MycpuScalar
