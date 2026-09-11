import Xv6.Kernel.PushOffCsrPure
import Xv6.Kernel.PushOffCsrPlan
import Xv6.Kernel.MycpuRegimeShellResources
import MachCSL.Logic.SupervisorBitsLink

namespace Xv6.Kernel.PushOffCsr
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

omit [Platform] in
private theorem frame_facts era cpu ms :
    iprop(MycpuRegimeShell.bitFrame capacity era cpu ms ⊢
      ⌜SupervisorBits.MsFacts ms ∧ _get_Mstatus_SIE ms = 0#1⌝) := by
  unfold MycpuRegimeShell.bitFrame SupervisorBits.offToken SupervisorBits.armBit SupervisorBits.sieBit
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro ⟨Hsie,_,%facts,Hoff⟩
  ihave %off := (SupervisorBits.actual capacity.supervisorBits).agree
    (SupervisorBits.namesOfEra era cpu).sie SupervisorBits.half SupervisorBits.eighth
    (_get_Mstatus_SIE ms) 0#1 $$ Hsie Hoff
  ipureintro
  exact ⟨facts,off⟩

theorem wp_body shares control values (config : Config control)
    image fixed whole gen era cpu regime (frame : IProp GF)
    (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values shares -∗ frame -∗
      (resources capacity era cpu regime control values shares frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (body >>= continuation)) post) := by
  iintro Hcert Hpacket Hframe Hfinish
  ihave ⟨Hcells,Hbits,Hz,Htr⟩ :=
    (MycpuRegimeShell.partition capacity era cpu regime control values shares).mp $$ Hpacket
  ihave %⟨facts,off⟩ := frame_facts capacity era cpu (control .mstatus) $$ Hbits
  have plan := body_plan (MycpuRegimeShell.footprint shares) (entry control cpu values)
    shares.privilege shares.misa
    (by simp [MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint])
    (by simp [MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint])
    (by simp [MycpuRegimeShell.footprint])
    (by change (.x15, DFrac.own 1) ∈ MycpuRegimeShell.controlFootprint shares ++ [(Register.mstatus, DFrac.own 1)] ++ MycpuRegimeShell.gprFootprint
        exact List.mem_append_right _ (by decide))
    (show Config (entry control cpu values) from config) facts off
  rw [← after_entry] at plan
  iapply RegisterPlan.fold capacity.machine (MycpuRegimeShell.footprint shares)
    (MycpuRegimeShell.footprint_unique shares) image fixed whole gen era cpu
    (entry control cpu values) _ _ continuation post plan $$ Hcert Hcells
  iintro %result %after %done Hcells
  rcases done with ⟨rfl,rfl⟩
  ihave Hpacket := (MycpuRegimeShell.partition capacity era cpu regime
    control (afterValues control values) shares).mpr $$ [Hcells Hbits Hz Htr]
  · rw [zero]
    iframe
  iapply Hfinish
  iunfold resources
  iframe

theorem actual : Spec capacity := ⟨wp_body capacity⟩

theorem pureSpec : PureSpec where
  instruction := instruction
  entry := after_entry
  other := other
  zero := zero
  pinnedTP := pinned_tp
  plan := body_plan

end Xv6.Kernel.PushOffCsr
