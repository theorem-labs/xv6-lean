import MachCSL.Logic.SupervisorAddressSpec
import MachCSL.Logic.SupervisorAddressPlan

namespace MachCSL.Logic.SupervisorAddress
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_transform (shares : Shares) (rs : RegisterFile) (mode : SATPMode) (config : Config rs mode)
    (address : BitVec 64) (kind : Kind) image fixed whole gen era cpu
    (continuation : virtaddr → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu rs shares -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Virtaddr address))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address kind >>= continuation)) post) := by
  iintro Hcert Hregs Hcontinue
  iapply RegisterPlan.fold capacity (footprint shares) (footprint_unique shares)
    image fixed whole gen era cpu rs (program address kind) _ continuation post
    (program_plan shares rs mode config address kind) $$ Hcert Hregs
  iintro %value %file %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hcontinue $$ Hregs

theorem actual : Spec capacity := ⟨wp_transform capacity⟩

end MachCSL.Logic.SupervisorAddress
