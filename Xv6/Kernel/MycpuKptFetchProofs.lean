import Xv6.Kernel.MycpuKptFetchResources

namespace Xv6.Kernel.MycpuKptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_fetch shares control values (config : Config control) i
    (pc : control .PC = MycpuDecode.address i)
    tier image fixed whole gen era cpu (N : Namespace) root rr (frame : IProp GF)
    (continuation : FetchResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu control values shares N root tier i rr frame continuation post -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hpacket #Hcode Hresv Hframe Hfinish
  ihave ⟨Hcells,Hsaved,Hresidue⟩ := (packet_partition capacity era cpu control values shares N root).mp $$ Hpacket
  iunfold packetFrame at Hsaved
  icases Hsaved with ⟨Hrest,Hbits,Hz⟩
  iunfold MycpuRegimeShell.bitFrame at Hbits
  icases Hbits with ⟨Hsie,Hsret,%facts,Hoff⟩
  ihave Hsaved : packetFrame capacity era cpu control values shares $$ [Hrest Hsie Hsret Hoff Hz]
  · iunfold packetFrame
    iunfold MycpuRegimeShell.bitFrame
    iframe Hrest Hsie Hsret Hoff Hz
    ipureintro; exact facts
  have entryPC : entry control cpu values .PC = MycpuDecode.address i := pc
  ihave Hinstr := code_instruction capacity era tier i $$ Hcode
  ihave Hinstr' : KptFetch.instrBytes capacity.translation era tier (entry control cpu values .PC) (result i) $$ [Hinstr]
  · rw [entryPC]; iexact Hinstr
  iapply KptFetch.wp_fetch capacity.translation (fetchShares shares) (entry control cpu values)
    (configuration control cpu values config facts) tier (result i) image fixed whole gen era cpu N root rr
    continuation post $$ Hcert Hcells Hresidue Hinstr' Hresv
  iunfold KptFetch.finish
  rw [entryPC]
  iunfold finish at Hfinish
  iapply KptFetch.guardChunks_mono $$ [Hsaved Hframe] Hfinish
  iintro %trace Hdone Hresources
  iunfold KptFetch.resources at Hresources
  icases Hresources with ⟨Hcells,Hresidue,Hresv,Hreceipts,_⟩
  ihave Hpacket := (packet_partition capacity era cpu control values shares N root).mpr $$ [Hcells Hsaved Hresidue]
  · iframe Hcells Hsaved Hresidue
  iapply Hdone $$ [Hpacket Hresv Hreceipts Hframe]
  iunfold resources
  iframe Hpacket Hcode Hresv Hreceipts Hframe

theorem actual : Spec capacity := ⟨wp_fetch capacity⟩

end Xv6.Kernel.MycpuKptFetch
