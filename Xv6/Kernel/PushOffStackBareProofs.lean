import Xv6.Kernel.PushOffStackBareResources
import Xv6.Kernel.PushOffStackWordProofs
import MachCSL.Logic.SupervisorBareReadLink
import MachCSL.Logic.SupervisorBareWriteLink

namespace Xv6.Kernel.PushOffStack.Bare
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

omit [Platform] in
private theorem collect era cpu control values s kind slot ξ old rr view satp pmp
    (mode : _get_Satp64_Mode (Mk_Satp64 satp) = 0#4) (tor : SupervisorPmp.TorRam pmp) frame :
    iprop(⊢ RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry (patch control satp pmp) cpu (afterMap kind slot values old)) (bareFootprint s slot) -∗
      packetFrame capacity era cpu control values s slot -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ (address cpu values slot) (.own 1)
        (KptMemory.valueAfter kind old (sourceValue cpu values slot)) -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
        (afterReservation .bare kind (address cpu values slot) rr ()) -∗
      Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
      closeIdentity capacity era ξ (address cpu values slot) -∗ frame -∗
      resources capacity era cpu .bare control values s kind slot .identity ξ old rr () view frame) := by
  iintro Hregs Hsaved Hrun Hword Hresv Hview Hclose Hframe
  have same : packetFrame capacity era cpu control (afterMap kind slot values old) s slot =
      packetFrame capacity era cpu control values s slot := by
    cases kind
    · exact packet_frame_load capacity era cpu control values s slot old
    · rfl
  ihave Hsaved : packetFrame capacity era cpu control (afterMap kind slot values old) s slot $$ [Hsaved]
  · rw [same]; iexact Hsaved
  ihave Hpacket := (packet_partition capacity era cpu control (afterMap kind slot values old) s slot).mpr $$ [Hregs Hsaved]
  · iexists satp,pmp
    iframe
    isplit
    · ipureintro; exact mode
    · ipureintro; exact tor
  iunfold closeIdentity at Hclose
  ihave Hword := Hclose $$ %(KptMemory.valueAfter kind old (sourceValue cpu values slot)) Hword
  iunfold resources
  isimp only [receipts]
  iframe

private theorem wp_tail s control values kind slot ξ old rr view satp pmp
    (mode : _get_Satp64_Mode (Mk_Satp64 satp) = 0#4) (tor : SupervisorPmp.TorRam pmp)
    image fixed whole gen era cpu frame (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry (patch control satp pmp) cpu values) (bareFootprint s slot) -∗
      packetFrame capacity era cpu control values s slot -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ (address cpu values slot) (.own 1)
        (KptMemory.valueAfter kind old (sourceValue cpu values slot)) -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
        (afterReservation .bare kind (address cpu values slot) rr ()) -∗
      Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
      closeIdentity capacity era ξ (address cpu values slot) -∗ frame -∗
      (resources capacity era cpu .bare control values s kind slot .identity ξ old rr () view frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (tail kind slot (KptMemory.result kind old) >>= continuation)) post) := by
  iintro #Hcert Hregs Hsaved Hrun Hword Hresv Hview Hclose Hframe Hfinish
  cases kind with
  | store =>
    isimp only [tail,KptMemory.result,storeTail,BootPmp.sail_pure_bind]
    iapply Hfinish
    have build := collect capacity era cpu control values s .store slot ξ old rr view satp pmp mode tor frame
    simp only [afterMap] at build
    iapply build $$ Hregs Hsaved Hrun Hword Hresv Hview Hclose Hframe
  | load =>
    isimp only [tail,KptMemory.result]
    iapply RegisterPlan.fold capacity.machine (bareFootprint s slot) (bare_footprint_unique s slot)
      image fixed whole gen era cpu (entry (patch control satp pmp) cpu values) _ _ continuation post
      (load_tail_plan s control satp pmp cpu values slot old) $$ Hcert Hregs
    iintro %result %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply Hfinish
    iapply collect capacity era cpu control values s .load slot ξ old rr view satp pmp mode tor frame
      $$ Hregs Hsaved Hrun Hword Hresv Hview Hclose Hframe

private theorem wp_memory s control values (config : Config control) kind slot ξ old rr satp pmp
    (mode : _get_Satp64_Mode (Mk_Satp64 satp) = 0#4) (tor : SupervisorPmp.TorRam pmp)
    image fixed whole gen era cpu frame (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry (patch control satp pmp) cpu values) (bareFootprint s slot) -∗
      packetFrame capacity era cpu control values s slot -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatum.word capacity.translation era .identity ξ (address cpu values slot) (.own 1) old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu .bare control values s kind slot .identity ξ old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (KptMemory.program kind (address cpu values slot) (sourceValue cpu values slot) >>=
          fun result => tail kind slot result >>= continuation)) post) := by
  iintro #Hcert Hregs Hsaved Hrun Hword Hresv Hframe Hfinish
  iunfold finish at Hfinish
  iunfold packetFrame at Hsaved
  icases Hsaved with ⟨Hrest,Hbits,Hz⟩
  iunfold MycpuRegimeShell.bitFrame at Hbits
  icases Hbits with ⟨Hsie,Hsret,%facts,Hoff⟩
  ihave Hsaved : packetFrame capacity era cpu control values s slot $$ [Hrest Hsie Hsret Hoff Hz]
  · iunfold packetFrame
    iunfold MycpuRegimeShell.bitFrame
    iframe
    ipureintro; exact facts
  ihave ⟨%wordFacts,Hword,Hclose⟩ := identity_word capacity era ξ (address cpu values slot) old $$ Hword
  rw [KptMemory.program_factor,BootPmp.sail_bind_assoc]
  iapply RegisterPlan.fold capacity.machine (bareFootprint s slot) (bare_footprint_unique s slot)
    image fixed whole gen era cpu (entry (patch control satp pmp) cpu values) _ _ _ post
    (transform_plan s slot _ kind (address cpu values slot) (transform_config control satp pmp cpu values config facts mode)) $$ Hcert Hregs
  iintro %va %after %same Hregs
  rcases same with ⟨rfl,rfl⟩
  ihave ⟨Hmem,Hoperands⟩ := (cells_memory capacity era cpu (entry (patch control satp pmp) cpu values) s slot).mp $$ Hregs
  cases kind with
  | load =>
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu
      (SupervisorBareRead.program (address cpu values slot) >>= fun result => loadTail slot result >>= continuation)) post)
    iapply (SupervisorBareRead.nativeSpec capacity.machine).read (memoryShares s)
      (entry (patch control satp pmp) cpu values) (address cpu values slot) MycpuBare.ramRegion
      (read_config control satp pmp cpu values _ config facts mode tor wordFacts.2)
      image fixed whole gen era cpu ξ (.own 1) old (fun result => loadTail slot result >>= continuation) post
      $$ Hcert Hmem Hrun Hword
    iintro !> %view Hmem Hrun Hword Hview
    ihave Hregs := (cells_memory capacity era cpu (entry (patch control satp pmp) cpu values) s slot).mpr $$ [Hmem Hoperands]
    · iframe
    have gate := wp_tail capacity s control values .load slot ξ old rr view satp pmp mode tor
      image fixed whole gen era cpu frame continuation post
    simp only [KptMemory.valueAfter,afterReservation,tail,KptMemory.result] at gate
    iapply gate $$ Hcert Hregs Hsaved Hrun Hword Hresv Hview Hclose Hframe
    iintro Hresources
    iapply Hfinish $$ %view Hresources
  | store =>
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu
      (SupervisorBareWrite.program (address cpu values slot) (sourceValue cpu values slot) >>= fun result => storeTail result >>= continuation)) post)
    iapply (SupervisorBareWrite.nativeSpec capacity.machine).write (memoryShares s)
      (entry (patch control satp pmp) cpu values) (address cpu values slot) MycpuBare.ramRegion
      (write_config control satp pmp cpu values _ config facts mode tor wordFacts.2)
      image fixed whole gen era cpu ξ old (sourceValue cpu values slot) rr
      (fun result => storeTail result >>= continuation) post $$ Hcert Hmem Hrun Hword Hresv
    iintro !> %view Hmem Hrun Hword Hresv Hview
    ihave Hregs := (cells_memory capacity era cpu (entry (patch control satp pmp) cpu values) s slot).mpr $$ [Hmem Hoperands]
    · iframe
    have gate := wp_tail capacity s control values .store slot ξ old rr view satp pmp mode tor
      image fixed whole gen era cpu frame continuation post
    simp only [KptMemory.valueAfter,afterReservation,tail,KptMemory.result] at gate
    iapply gate $$ Hcert Hregs Hsaved Hrun Hword Hresv Hview Hclose Hframe
    iintro Hresources
    iapply Hfinish $$ %view Hresources

theorem wp_body s control values (config : Config control) kind slot ξ old rr
    image fixed whole gen era cpu frame (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu .bare control values s -∗ TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatum.word capacity.translation era .identity ξ (address cpu values slot) (.own 1) old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu .bare control values s kind slot .identity ξ old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (PushOffStack.body kind slot >>= continuation)) post) := by
  iintro #Hcert Hpacket Hrun Hword Hresv Hframe Hfinish
  ihave ⟨%satp,%pmp,%mode,%tor,Hregs,Hsaved⟩ := (packet_partition capacity era cpu control values s slot).mp $$ Hpacket
  cases kind with
  | load =>
    isimp only [load_factor,BootPmp.sail_bind_assoc]
    iapply RegisterPlan.fold capacity.machine (bareFootprint s slot) (bare_footprint_unique s slot)
      image fixed whole gen era cpu (entry (patch control satp pmp) cpu values) _ _ _ post
      (sp_plan s control satp pmp cpu values slot) $$ Hcert Hregs
    iintro %sp %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu
      (KptMemory.program .load (address cpu values slot) (sourceValue cpu values slot) >>= fun result => tail .load slot result >>= continuation)) post)
    iapply wp_memory capacity s control values config .load slot ξ old rr satp pmp mode tor
      image fixed whole gen era cpu frame continuation post $$ Hcert Hregs Hsaved Hrun Hword Hresv Hframe Hfinish
  | store =>
    isimp only [store_factor,BootPmp.sail_bind_assoc]
    iapply RegisterPlan.fold capacity.machine (bareFootprint s slot) (bare_footprint_unique s slot)
      image fixed whole gen era cpu (entry (patch control satp pmp) cpu values) _ _ _ post
      (source_plan s control satp pmp cpu values slot) $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply RegisterPlan.fold capacity.machine (bareFootprint s slot) (bare_footprint_unique s slot)
      image fixed whole gen era cpu (entry (patch control satp pmp) cpu values) _ _ _ post
      (sp_plan s control satp pmp cpu values slot) $$ Hcert Hregs
    iintro %sp %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu
      (KptMemory.program .store (address cpu values slot) (sourceValue cpu values slot) >>= fun result => tail .store slot result >>= continuation)) post)
    iapply wp_memory capacity s control values config .store slot ξ old rr satp pmp mode tor
      image fixed whole gen era cpu frame continuation post $$ Hcert Hregs Hsaved Hrun Hword Hresv Hframe Hfinish

end Xv6.Kernel.PushOffStack.Bare
