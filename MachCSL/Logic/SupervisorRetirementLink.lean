import MachCSL.Logic.SupervisorRetirementProofs
import MachCSL.Logic.RestartWPProofs

namespace MachCSL.Logic.SupervisorRetirement
open Iris Iris.BI MachCSL.Machine

/-- All primitive contracts use the existing native register camera and rules. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

/-- The source boundary owns an arbitrary reservation. The actual restart node
clears it, preserves all nine register resources, and universally chooses the
next cycle's clock flag. A pure residual is not treated as a terminal value. -/
theorem wp_pcIs_restart {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) image fixed whole gen era cpu pc post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      pcIs capacity era cpu pc -∗
      ▷ (∀ tick : Bool,
        pcRegs capacity.era.registers (era.registers cpu) pc -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (.pure ())) post) := by
  rw [(pcIs_parts capacity era cpu pc).to_eq]
  iintro Hcert ⟨Hregs, Hresv⟩ Hcontinue
  iapply RestartWP.wp_restart capacity image fixed whole gen era cpu post $$ Hcert Hresv
  iintro !> %tick Hresv
  iapply Hcontinue $$ %tick Hregs Hresv

end MachCSL.Logic.SupervisorRetirement
