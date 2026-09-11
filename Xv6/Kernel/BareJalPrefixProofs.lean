import Xv6.Kernel.BareJalRules
import Xv6.Kernel.KptJalPrepareProofs
namespace Xv6.Kernel.BareJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)
theorem wp_prefix {A : Type} control after values cpu (sameMs : after .mstatus = control .mstatus)
    (program body : SailM A)
    (cut : MycpuActive.Prefix (MycpuRegimeShell.footprint shares) (entry control cpu values)
      program body (entry after cpu values))
    image fixed whole gen era (frame : IProp GF)
    (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu control values -∗ frame -∗
      (packet capacity era cpu after values -∗ frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (body >>= continuation)) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hpacket Hframe Hfinish
  iunfold packet at Hpacket
  ihave ⟨Hcells,Hbits,Hz,Htr⟩ := (MycpuRegimeShell.partition capacity era cpu .bare control values shares).mp $$ Hpacket
  iapply MycpuActive.Prefix.fold capacity.machine (MycpuRegimeShell.footprint shares) (MycpuRegimeShell.footprint_unique shares)
    (entry control cpu values) (entry after cpu values) program body cut image fixed whole gen era cpu continuation post $$ Hcert Hcells
  iintro Hcells
  ihave Hpacket := (MycpuRegimeShell.partition capacity era cpu .bare after values shares).mpr $$ [Hcells Hbits Hz Htr]
  · rw [sameMs]
    iframe
  iunfold packet at Hfinish
  iapply Hfinish $$ Hpacket Hframe

end Xv6.Kernel.BareJal
