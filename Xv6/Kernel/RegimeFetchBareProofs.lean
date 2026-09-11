import Xv6.Kernel.RegimeFetchSpec
import Xv6.Kernel.BareFetchLink
import Xv6.Kernel.BareJalRules

namespace Xv6.Kernel.RegimeFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

instance code_persistent era tier pc result : Persistent (code capacity era tier pc result) := by
  unfold code; infer_instance

theorem wp_bare control values (config : Config control) result ξ rr image fixed whole gen era cpu
    (frame : IProp GF) continuation post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu .bare control values -∗ code capacity era .identity (control .PC) result -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu .bare control values .identity result ξ rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hresv Hframe Hfinish
  ihave Hbare : BareJal.packet capacity era cpu control values $$ [Hpacket]
  · iunfold packet at Hpacket
    iunfold BareJal.packet
    iexact Hpacket
  ihave ⟨%satp,%pmp,%mode,%tor,Hcells,Hsaved⟩ :=
    (BareJal.partition capacity era cpu control values).mp $$ Hbare
  iunfold BareJal.fetchFrame at Hsaved
  icases Hsaved with ⟨Hrest,Hbits,Hz⟩
  iunfold MycpuRegimeShell.bitFrame at Hbits
  icases Hbits with ⟨Hsie,Hsret,%facts,Hoff⟩
  ihave Hsaved : BareJal.fetchFrame capacity era cpu (BareJal.patch control satp pmp) values
      $$ [Hrest Hsie Hsret Hoff Hz]
  · iunfold BareJal.fetchFrame
    iunfold MycpuRegimeShell.bitFrame
    iframe Hrest Hsie Hsret Hoff Hz
    ipureintro; exact facts
  have entryPC : entry (BareJal.patch control satp pmp) cpu values .PC = control .PC := rfl
  ihave Hinstr : BareFetch.code capacity.translation era
      (entry (BareJal.patch control satp pmp) cpu values .PC) result $$ []
  · iunfold BareFetch.code
    rw [entryPC]
    iunfold code at Hcode
    iexact Hcode
  iapply BareFetch.wp_fetch capacity.translation BareJal.fetchShares
    (entry (BareJal.patch control satp pmp) cpu values)
    (BareJal.fetch_config control cpu values config satp pmp mode tor facts) result
    image fixed whole gen era cpu ξ continuation post $$ Hcert Hcells Hrun Hinstr
  iunfold BareFetch.finish
  rw [entryPC]
  iunfold BareFetch.guards
  iunfold finish at Hfinish
  isimp only [guards, BareFetch.guards] at Hfinish
  iapply BareJalFetch.guardReads_mono $$ [Hsaved Hresv Hframe] Hfinish
  iintro %views Hdone Hresources
  iunfold BareFetch.resources at Hresources
  icases Hresources with ⟨Hcells,Hrun,_,Hreceipts⟩
  ihave Hpacket := (BareJal.partition capacity era cpu control values).mpr $$ [Hcells Hsaved]
  · iexists satp,pmp
    iframe
    isplitr
    · ipureintro; exact mode
    ipureintro; exact tor
  iapply Hdone
  iunfold resources
  isimp only [afterReservation, receipts]
  iunfold packet
  iunfold BareJal.packet at Hpacket
  iframe Hpacket Hcode Hrun Hresv Hreceipts Hframe
end Xv6.Kernel.RegimeFetch
