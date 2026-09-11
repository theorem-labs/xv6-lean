import Xv6.Kernel.PushOffWord4Rules
namespace Xv6.Kernel.PushOffWord4
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_memory_kpt shares control values N root (config : Config (.kpt N root) control)
    op tier ξ dq old rr (full : kind op = .store → dq = .own 1)
    image fixed whole gen era cpu frame (continuation : KptMemory4.Result (kind op) → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatumWord4.word capacity.translation era tier ξ (address cpu values op) dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      memoryFinish capacity image fixed whole gen era cpu (.kpt N root) control values shares op tier ξ dq old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (KptMemory4.program (kind op) (address cpu values op) (sourceValue cpu values) >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hpacket Hrun Hword Hresv Hframe Hfinish
  ihave ⟨Hregs,Htr,Hsaved⟩ := (packet_kpt capacity era cpu control values shares N root).mp $$ Hpacket
  iunfold packetFrame at Hsaved
  icases Hsaved with ⟨Hrest,Hbits,Hz⟩
  iunfold MycpuRegimeShell.bitFrame at Hbits
  icases Hbits with ⟨Hsie,Hsret,%facts,Hoff⟩
  ihave Hsaved : packetFrame capacity era cpu control values shares $$ [Hrest Hsie Hsret Hoff Hz]
  · iunfold packetFrame
    iunfold MycpuRegimeShell.bitFrame
    iframe
    ipureintro; exact facts
  ihave ⟨Haux,Hoperands⟩ := (cells_memory capacity era cpu (entry control cpu values) shares).mp $$ Hregs
  iapply (KptMemory4.nativeSpec capacity.translation).transformed (memoryShares shares)
    (entry control cpu values) (kpt_ambient control cpu values N root config facts)
    (kind op) tier ξ (address cpu values op) dq old (sourceValue cpu values) rr full
    image fixed whole gen era cpu N root continuation post $$ Hcert Haux Htr Hrun Hword Hresv
  ieval (change _ ⊢ MycpuKptMemory.guards _)
  iapply MycpuKptMemory.guards_frame
    (P := fun ppn data outcome => iprop(⌜KptMemory4.CompletedFacts (entry control cpu values) data root (kind op) (address cpu values op) ppn outcome⌝ -∗ ▷ ∀ view,
      memoryResources capacity era cpu (.kpt N root) control values shares op tier ξ dq old rr outcome view frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (KptMemory4.result (kind op) old))) post))
    (R := iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry control cpu values) [(.x10,.own 1),(.x15,.own 1)] ∗ packetFrame capacity era cpu control values shares ∗ frame))
    (next := ?_) $$ [Hoperands Hsaved Hframe Hfinish]
  · intro ppn data outcome
    unfold KptMemory4.continueWith
    iintro ⟨⟨Hoperands,Hsaved,Hframe⟩,Hfinish⟩ %done
    ihave Hfinish := Hfinish $$ %done
    iintro !> %view Hdata
    iunfold KptMemory4.resources at Hdata
    icases Hdata with ⟨Haux,Htr,Hrun,Hword,Hresv,Hreceipts,Hview⟩
    ihave Hregs := (cells_memory capacity era cpu (entry control cpu values) shares).mpr $$ [Haux Hoperands]
    · iframe
    ihave Hpacket := (packet_kpt capacity era cpu control values shares N root).mpr $$ [Hregs Htr Hsaved]
    · iframe
    iapply Hfinish $$ %view
    iunfold memoryResources
    isimp only [afterReservation,receipts]
    iframe
  · iframe Hoperands Hsaved Hframe
    isimp only [memoryFinish,guards] at Hfinish
    iexact Hfinish

theorem wp_memory_bare shares control values (config : Config .bare control)
    op ξ dq old rr (full : kind op = .store → dq = .own 1)
    image fixed whole gen era cpu frame (continuation : KptMemory4.Result (kind op) → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu .bare control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatumWord4.word capacity.translation era .identity ξ (address cpu values op) dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      memoryFinish capacity image fixed whole gen era cpu .bare control values shares op .identity ξ dq old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (KptMemory4.program (kind op) (address cpu values op) (sourceValue cpu values) >>= continuation)) post) := by
  iintro #Hcert Hpacket Hrun Hword Hresv Hframe Hfinish
  isimp only [memoryFinish,guards] at Hfinish
  ihave Hopened := (packet_bare capacity era cpu control values shares).mp $$ Hpacket
  iunfold barePacket at Hopened
  icases Hopened with ⟨%satp,%pmp,%bareFacts,Hcells,Hbits,Hz⟩
  iunfold MycpuRegimeShell.bitFrame at Hbits
  icases Hbits with ⟨Hsie,Hsret,%facts,Hoff⟩
  ihave Hbits : MycpuRegimeShell.bitFrame capacity era cpu (control .mstatus) $$ [Hsie Hsret Hoff]
  · iunfold MycpuRegimeShell.bitFrame
    iframe
    ipureintro; exact facts
  ihave ⟨Hcells,Hrest⟩ := (bare_cells_partition capacity era cpu
    (entry (MycpuBareSource.patch control satp pmp) cpu values) shares).mp $$ Hcells
  ihave ⟨Haux,Hoperands⟩ := (cells_bare_memory capacity era cpu
    (entry (MycpuBareSource.patch control satp pmp) cpu values) shares).mp $$ Hcells
  ihave ⟨%wordFacts,Hwindow,Hclose⟩ := identity_word capacity era ξ (address cpu values op) dq old $$ Hword
  iapply (PushOffWord4Bare.nativeSpec capacity.machine).transformed (bareShares shares)
    (entry (MycpuBareSource.patch control satp pmp) cpu values)
    (bare_config control cpu values satp pmp config facts bareFacts.1 bareFacts.2)
    (kind op) ξ (address cpu values op) dq old (sourceValue cpu values) rr wordFacts.1 wordFacts.2 full
    image fixed whole gen era cpu continuation post $$ Hcert Haux Hrun Hwindow Hresv
  iunfold PushOffWord4Bare.finish
  iintro !> %view Hdata
  iunfold PushOffWord4Bare.resources at Hdata
  icases Hdata with ⟨Haux,Hrun,Hwindow,Hresv,Hview⟩
  ihave Hword := Hclose $$ %(KptMemory4.valueAfter (kind op) old (sourceValue cpu values)) Hwindow
  ihave Hcells := (cells_bare_memory capacity era cpu (entry (MycpuBareSource.patch control satp pmp) cpu values) shares).mpr $$ [Haux Hoperands]
  · iframe
  ihave Hcells := (bare_cells_partition capacity era cpu (entry (MycpuBareSource.patch control satp pmp) cpu values) shares).mpr $$ [Hcells Hrest]
  · iframe
  ihave Hopened : barePacket capacity era cpu control values shares $$ [Hcells Hbits Hz]
  · iunfold barePacket
    iexists satp,pmp
    iframe
    ipureintro; exact bareFacts
  ihave Hpacket := (packet_bare capacity era cpu control values shares).mpr $$ Hopened
  iapply Hfinish $$ %view
  iunfold memoryResources
  isimp only [afterReservation,receipts]
  iframe

theorem wp_memory regime shares control values (config : Config regime control)
    op tier ξ dq old rr (admitted : MycpuRegimeShell.Admits regime tier)
    (full : kind op = .store → dq = .own 1)
    image fixed whole gen era cpu frame (continuation : KptMemory4.Result (kind op) → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatumWord4.word capacity.translation era tier ξ (address cpu values op) dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      memoryFinish capacity image fixed whole gen era cpu regime control values shares op tier ξ dq old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (KptMemory4.program (kind op) (address cpu values op) (sourceValue cpu values) >>= continuation)) post) := by
  cases regime with
  | kpt N root => exact wp_memory_kpt capacity shares control values N root config op tier ξ dq old rr full image fixed whole gen era cpu frame continuation post
  | bare =>
    cases tier with
    | full => contradiction
    | identity => exact wp_memory_bare capacity shares control values config op ξ dq old rr full image fixed whole gen era cpu frame continuation post
end Xv6.Kernel.PushOffWord4
