import Xv6.Kernel.RegimeFetchBareProofs
import Xv6.Kernel.KptJalResources

namespace Xv6.Kernel.RegimeFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem wp_kpt control values (config : Config control) tier result ξ rr image fixed whole gen era cpu N root
    (frame : IProp GF) continuation post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values -∗ code capacity era tier (control .PC) result -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu (.kpt N root) control values tier result ξ rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hresv Hframe Hfinish
  iunfold packet at Hpacket
  ihave ⟨Hcells,Hsaved,Hresidue⟩ :=
    (MycpuKptFetch.packet_partition capacity era cpu control values shares N root).mp $$ Hpacket
  iunfold MycpuKptFetch.packetFrame at Hsaved
  icases Hsaved with ⟨Hrest,Hbits,Hz⟩
  iunfold MycpuRegimeShell.bitFrame at Hbits
  icases Hbits with ⟨Hsie,Hsret,%facts,Hoff⟩
  ihave Hsaved : MycpuKptFetch.packetFrame capacity era cpu control values shares $$ [Hrest Hsie Hsret Hoff Hz]
  · iunfold MycpuKptFetch.packetFrame
    iunfold MycpuRegimeShell.bitFrame
    iframe Hrest Hsie Hsret Hoff Hz
    ipureintro; exact facts
  ihave Hinstr : KptFetch.instrBytes capacity.translation era tier (entry control cpu values .PC) result $$ []
  · rw [show entry control cpu values .PC = control .PC from rfl]
    iunfold code at Hcode; iexact Hcode
  iapply KptFetch.wp_fetch capacity.translation (MycpuKptFetch.fetchShares shares) (entry control cpu values)
    (MycpuKptFetch.configuration control cpu values (MycpuKptCycle.fetch_config control config) facts)
    tier result image fixed whole gen era cpu N root rr continuation post $$ Hcert Hcells Hresidue Hinstr Hresv
  iunfold KptFetch.finish
  rw [show entry control cpu values .PC = control .PC from rfl]
  iunfold finish at Hfinish
  isimp only [guards] at Hfinish
  iapply KptFetch.guardChunks_mono $$ [Hsaved Hrun Hframe] Hfinish
  iintro %trace Hdone Hresources
  iunfold KptFetch.resources at Hresources
  icases Hresources with ⟨Hcells,Hresidue,Hresv,Hreceipts,_⟩
  ihave Hpacket := (MycpuKptFetch.packet_partition capacity era cpu control values shares N root).mpr
      $$ [Hcells Hsaved Hresidue]
  · iframe
  iapply Hdone
  iunfold resources
  isimp only [afterReservation, receipts]
  iunfold packet
  iframe Hpacket Hcode Hrun Hresv Hreceipts Hframe
end Xv6.Kernel.RegimeFetch
