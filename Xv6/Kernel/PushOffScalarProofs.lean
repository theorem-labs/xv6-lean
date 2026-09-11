import Xv6.Kernel.PushOffScalarPlan
import Xv6.Kernel.MycpuRegimeShellResources

namespace Xv6.Kernel.PushOffScalar
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem wp_body instruction shares control values (config : Config instruction control)
    image fixed whole gen era cpu regime (frame : IProp GF)
    (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values shares -∗ frame -∗
      (resources capacity era cpu regime instruction control values shares frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (body instruction >>= continuation)) post) := by
  iintro Hcert Hpacket Hframe Hfinish
  ihave ⟨Hcells,Hbits,Hz,Htr⟩ :=
    (MycpuRegimeShell.partition capacity era cpu regime control values shares).mp $$ Hpacket
  iapply RegisterPlan.fold capacity.machine (MycpuRegimeShell.footprint shares)
    (MycpuRegimeShell.footprint_unique shares) image fixed whole gen era cpu
    (entry control cpu values) _ _ continuation post
    (body_plan instruction shares control cpu values config) $$ Hcert Hcells
  iintro %result %after %done Hcells
  rcases done with ⟨rfl,rfl⟩
  ihave Hpacket := (MycpuRegimeShell.partition capacity era cpu regime
    (afterControl instruction control cpu values) (afterValues instruction cpu values) shares).mpr
    $$ [Hcells Hbits Hz Htr]
  · rw [control_other instruction control cpu values .mstatus (by decide), zero]
    iframe
  iapply Hfinish
  iunfold resources
  iframe

/-- The ordinary native register fold proves every actual subevent. -/
theorem actual : Spec capacity := ⟨wp_body capacity⟩

end Xv6.Kernel.PushOffScalar
