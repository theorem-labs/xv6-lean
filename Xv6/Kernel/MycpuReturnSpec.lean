import Xv6.Kernel.MycpuReturnDefs
import MachCSL.Logic.RegisterPlanSpec

namespace Xv6.Kernel.MycpuReturn
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  returns : ∀ shares (rs : RegisterFile), Config rs →
    ∀ image fixed whole gen era cpu (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares) -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (after rs) (footprint shares) -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (body >>= continuation)) post)

end Xv6.Kernel.MycpuReturn
