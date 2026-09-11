import Xv6.Kernel.PushOffStackRules

namespace Xv6.Kernel.PushOffStack.Kpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

private theorem wp_tail shares control values kind slot tier ξ dq old rr outcome view
    image fixed whole gen era cpu N root frame (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      KptMemory.resources capacity.translation era cpu (entry control cpu values) (memoryShares shares)
        N root kind tier ξ (address cpu values slot) dq old (sourceValue cpu values slot) rr outcome view -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) (entry control cpu values)
        [(.x2,.own 1),(register slot,.own 1)] -∗
      packetFrame capacity era cpu control values shares slot -∗ frame -∗
      (resources capacity era cpu control values shares N root kind slot tier ξ dq old rr outcome view frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (tail kind slot (KptMemory.result kind old) >>= continuation)) post) := by
  iintro #Hcert Hdata Hoperands Hsaved Hframe Hfinish
  iunfold KptMemory.resources at Hdata
  icases Hdata with ⟨Haux,Htr,Hrun,Hword,Hresv,Hreceipts,Hview⟩
  ihave Hregs := (cells_memory capacity era cpu (entry control cpu values) shares slot).mpr $$ [Haux Hoperands]
  · iframe
  cases kind with
  | store =>
    isimp only [tail, KptMemory.result, storeTail, BootPmp.sail_pure_bind]
    ihave Hpacket := (packet_partition capacity era cpu control values shares slot N root).mpr $$ [Hregs Hsaved Htr]
    · iframe
    iapply Hfinish
    iunfold resources
    isimp only [afterMap]
    iframe
  | load =>
    isimp only [tail, KptMemory.result]
    iapply RegisterPlan.fold capacity.machine (footprint shares slot) (footprint_unique shares slot)
      image fixed whole gen era cpu (entry control cpu values) _ _ continuation post
      (load_tail_plan shares control cpu values slot old) $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ihave Hsaved : packetFrame capacity era cpu control (afterMap .load slot values old) shares slot $$ [Hsaved]
    · rw [packet_frame_load]; iexact Hsaved
    ihave Hpacket := (packet_partition capacity era cpu control (afterMap .load slot values old) shares slot N root).mpr $$ [Hregs Hsaved Htr]
    · iframe
    iapply Hfinish
    iunfold resources
    iframe

private theorem wp_memory shares control values (config : Config control) kind slot tier ξ dq old rr
    (full : kind = .store → dq = .own 1)
    image fixed whole gen era cpu N root frame (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry control cpu values) (footprint shares slot) -∗
      packetFrame capacity era cpu control values shares slot -∗
      KptResidue.residue capacity.translation era cpu N root -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatum.word capacity.translation era tier ξ (address cpu values slot) dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu control values shares N root kind slot tier ξ dq old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (KptMemory.program kind (address cpu values slot) (sourceValue cpu values slot) >>=
          fun result => tail kind slot result >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hregs Hsaved Htr Hrun Hword Hresv Hframe Hfinish
  iunfold packetFrame at Hsaved
  icases Hsaved with ⟨Hrest,Hbits,Hz⟩
  iunfold MycpuRegimeShell.bitFrame at Hbits
  icases Hbits with ⟨Hsie,Hsret,%facts,Hoff⟩
  ihave Hsaved : packetFrame capacity era cpu control values shares slot $$ [Hrest Hsie Hsret Hoff Hz]
  · iunfold packetFrame
    iunfold MycpuRegimeShell.bitFrame
    iframe
    ipureintro; exact facts
  ihave ⟨Haux,Hoperands⟩ := (cells_memory capacity era cpu (entry control cpu values) shares slot).mp $$ Hregs
  iapply (KptMemory.nativeSpec capacity.translation).transformed (memoryShares shares) (entry control cpu values)
    (ambient control cpu values config facts) kind tier ξ (address cpu values slot) dq old
    (sourceValue cpu values slot) rr full image fixed whole gen era cpu N root
    (fun result => tail kind slot result >>= continuation) post $$ Hcert Haux Htr Hrun Hword Hresv
  ieval (change _ ⊢ guards _)
  iapply guards_frame (P := continueWith capacity image fixed whole gen era cpu control values shares N root kind slot tier ξ dq old rr frame continuation post) (R := iprop(MachineInterp.generationCertificate capacity.machine fixed gen era ∗ RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
    (entry control cpu values) [(.x2,.own 1),(register slot,.own 1)] ∗
    packetFrame capacity era cpu control values shares slot ∗ frame)) (next := ?_) $$ [Hoperands Hsaved Hframe Hfinish]
  · intro ppn data outcome
    unfold KptMemory.continueWith continueWith
    iintro ⟨⟨#Hcert,Hoperands,Hsaved,Hframe⟩,Hfinish⟩ %done
    ihave Hfinish := Hfinish $$ %done
    iintro !> %view Hdata
    iapply wp_tail capacity shares control values kind slot tier ξ dq old rr outcome view
      image fixed whole gen era cpu N root frame continuation post $$ Hcert Hdata Hoperands Hsaved Hframe
    iintro Hresources
    iapply Hfinish $$ %view Hresources
  · iframe Hcert Hoperands Hsaved Hframe
    isimp only [finish] at Hfinish
    iexact Hfinish

theorem wp_body : ∀ shares control values, Config control → ∀ kind slot tier ξ dq old rr,
    (kind = .store → dq = .own 1) →
    ∀ image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF)
      (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatum.word capacity.translation era tier ξ (address cpu values slot) dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu control values shares N root kind slot tier ξ dq old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (PushOffStack.body kind slot >>= continuation)) post) := by
  intro shares control values config kind slot tier ξ dq old rr full image fixed whole gen era cpu N root frame continuation post
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hpacket Hrun Hword Hresv Hframe Hfinish
  ihave ⟨Hregs,Hsaved,Htr⟩ := (packet_partition capacity era cpu control values shares slot N root).mp $$ Hpacket
  cases kind with
  | load =>
    isimp only [load_factor, BootPmp.sail_bind_assoc]
    iapply RegisterPlan.fold capacity.machine (footprint shares slot) (footprint_unique shares slot)
      image fixed whole gen era cpu (entry control cpu values) _ _ _ post
      (sp_plan shares control cpu values slot) $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (KptMemory.program .load (address cpu values slot) (sourceValue cpu values slot) >>= fun (result : KptMemory.Result .load) => tail .load slot result >>= continuation)) post)
    iapply wp_memory capacity shares control values config .load slot tier ξ dq old rr full
      image fixed whole gen era cpu N root frame continuation post
      $$ Hcert Hregs Hsaved Htr Hrun Hword Hresv Hframe Hfinish
  | store =>
    isimp only [store_factor, BootPmp.sail_bind_assoc]
    iapply RegisterPlan.fold capacity.machine (footprint shares slot) (footprint_unique shares slot)
      image fixed whole gen era cpu (entry control cpu values) _ _ _ post
      (source_plan shares control cpu values slot) $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply RegisterPlan.fold capacity.machine (footprint shares slot) (footprint_unique shares slot)
      image fixed whole gen era cpu (entry control cpu values) _ _ _ post
      (sp_plan shares control cpu values slot) $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (KptMemory.program .store (address cpu values slot) (sourceValue cpu values slot) >>= fun (result : KptMemory.Result .store) => tail .store slot result >>= continuation)) post)
    iapply wp_memory capacity shares control values config .store slot tier ξ dq old rr full
      image fixed whole gen era cpu N root frame continuation post
      $$ Hcert Hregs Hsaved Htr Hrun Hword Hresv Hframe Hfinish

end Xv6.Kernel.PushOffStack.Kpt
