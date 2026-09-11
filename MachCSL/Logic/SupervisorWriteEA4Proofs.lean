import MachCSL.Logic.SupervisorWriteEA4Spec
import MachCSL.Logic.SupervisorWriteEA4Plan

namespace MachCSL.Logic.SupervisorWriteEA4
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Native fold of the actual six reads. No ownership of memory or a chosen
memory result is needed by the write-address announcement. -/
theorem wp_announce (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region)
    image fixed whole gen era cpu (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu rs shares -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok ()))) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (program address >>= continuation)) post) := by
  iintro Hcert Hregs Hcontinue
  iapply RegisterPlan.fold capacity (footprint shares) (footprint_unique shares)
    image fixed whole gen era cpu rs (program address) _ continuation post
    (program_plan shares rs address region config) $$ Hcert Hregs
  iintro %value %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hcontinue $$ Hregs

theorem actual : Spec capacity := ⟨wp_announce capacity⟩

end MachCSL.Logic.SupervisorWriteEA4
