import Xv6.Kernel.MycpuOffResources
import Xv6.Kernel.MycpuBareSpec
import MachCSL.Logic.SupervisorBitsSpec

namespace Xv6.Kernel.MycpuOff
open Iris Iris.BI Iris.ProofMode MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
  (capacity : Capacity GF) (bits : SupervisorBits.Spec capacity.supervisorBits)
  (body : MycpuBare.Spec capacity.machine)

include bits body

theorem wp_function shares control values (config : EntryConfig control)
    image fixed whole gen era cpu ξ (oldRA oldS0 : BitVec 64) rr initialTick post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ MycpuBare.shared capacity.machine era -∗
      stackWords capacity era ξ control cpu values oldRA oldS0 -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜Result control cpu values after⌝ -∗
        resources capacity era cpu after (returnedMap values after) shares -∗
        TsoContextReadWP.running capacity.machine era cpu ξ -∗ MycpuBare.shared capacity.machine era -∗
        stackWords capacity era ξ control cpu values (values 1#5) (values 8#5) -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle initialTick)) post) := by
  iintro Hcert Hresources Hrun Hcode Hwords Hresv Hfinish
  iunfold resources at Hresources
  icases Hresources with ⟨Hcontrol, Hms, Hoff, Hgpr⟩
  iunfold SupervisorBits.msOwnAt at Hms
  ihave %off := bits.off (era.registers cpu) (SupervisorBits.namesOfEra era cpu) (control .mstatus) $$ Hms Hoff
  iunfold SupervisorBits.msOwn at Hms
  icases Hms with ⟨Hmsreg, Hsie, Hsret, %facts⟩
  isimp [Capacity.supervisorBits] at Hmsreg
  ihave ⟨Hregs, Hsaved, Hrest, Hz⟩ := (partition capacity era cpu control values shares).1 $$ [$Hcontrol $Hmsreg $Hgpr]
  iunfold stackWords at Hwords
  isimp [stackWords] at Hfinish
  have entryConfig := entry_config control cpu values config facts off
  iapply body.hart (cycleShares shares) (fun _ => .own 1) (entry control cpu values) entryConfig
    image fixed whole gen era cpu ξ oldRA oldS0 rr initialTick post (entry_tp control cpu values)
    $$ Hcert Hregs Hsaved Hrun Hcode Hwords Hresv
  iintro %after %result Hregs Hsaved Hrun Hcode Hwords Hresv %nextTick
  ihave ⟨Hcontrol, Hmsreg, Hgpr⟩ := reassemble capacity era cpu control values after shares result
    $$ [$Hregs $Hsaved $Hrest $Hz]
  have msSame : after .mstatus = control .mstatus := result.stable .mstatus (by decide)
  ihave Hms : SupervisorBits.msOwnAt capacity.supervisorBits era cpu (after .mstatus) $$ [Hmsreg Hsie Hsret]
  · iunfold SupervisorBits.msOwnAt
    iunfold SupervisorBits.msOwn
    rw [show capacity.supervisorBits.registers = capacity.machine.era.registers from rfl]
    iframe Hmsreg
    rw [msSame]
    iframe Hsie Hsret
    ipureintro
    exact facts
  ihave Hresources : resources capacity era cpu after (returnedMap values after) shares
    $$ [Hcontrol Hms Hoff Hgpr]
  · iunfold resources
    iframe
  isimp [show entry control cpu values .x1 = values 1#5 from rfl,
    show entry control cpu values .x8 = values 8#5 from rfl] at Hwords
  iapply Hfinish $$ %after %(returned_result control cpu values after result)
    Hresources Hrun Hcode Hwords Hresv %nextTick

theorem actual : Spec capacity := ⟨wp_function capacity bits body⟩

end Xv6.Kernel.MycpuOff
