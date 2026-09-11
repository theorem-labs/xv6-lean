import Xv6.Kernel.MycpuScalarDefs
import MachCSL.Logic.RegisterPlanSpec

namespace Xv6.Kernel.MycpuScalar
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  scalar : ∀ pcShare tpShare (i : Fin 9) image fixed whole gen era cpu rs
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs
        (footprint pcShare tpShare) -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (after i rs)
          (footprint pcShare tpShare) -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (body i >>= continuation)) post)

end Xv6.Kernel.MycpuScalar
