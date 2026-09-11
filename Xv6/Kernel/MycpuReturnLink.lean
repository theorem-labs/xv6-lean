import Xv6.Kernel.MycpuReturnSpec
import Xv6.Kernel.MycpuReturnProofs

namespace Xv6.Kernel.MycpuReturn
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_return (shares : Shares) (rs : RegisterFile) (config : Config rs)
    image fixed whole gen era cpu (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares) -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (after rs) (footprint shares) -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (body >>= continuation)) post) := by
  iintro Hcert Hregs Hcontinue
  iapply RegisterPlan.fold capacity (footprint shares) (footprint_unique shares)
    image fixed whole gen era cpu rs body _ continuation post
    (body_plan shares rs config) $$ Hcert Hregs
  iintro %value %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hcontinue $$ Hregs

theorem wp_return_pc (shares : Shares) (pcShare : DFrac) (rs : RegisterFile) (config : Config rs)
    image fixed whole gen era cpu (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (pcFootprint shares pcShare) -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (after rs) (pcFootprint shares pcShare) -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (body >>= continuation)) post) := by
  iintro Hcert Hregs Hcontinue
  iapply RegisterPlan.fold capacity (pcFootprint shares pcShare) (pcFootprint_unique shares pcShare)
    image fixed whole gen era cpu rs body _ continuation post
    (pc_body_plan shares pcShare rs config) $$ Hcert Hregs
  iintro %value %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hcontinue $$ Hregs

theorem wp_source (rs : RegisterFile) (source : SourceConfig rs)
    image fixed whole gen era cpu (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint sourceShares) -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) (after rs) (footprint sourceShares) -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (body >>= continuation)) post) :=
  wp_return capacity sourceShares rs (source_config rs source)
    image fixed whole gen era cpu continuation post

theorem nativeSpec : Spec capacity := ⟨wp_return capacity⟩

end Xv6.Kernel.MycpuReturn
