import Xv6.Kernel.PushOffWord4MemoryProofs
namespace Xv6.Kernel.PushOffWord4
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_tail regime shares control values op tier ξ dq old rr outcome view
    image fixed whole gen era cpu frame (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      memoryResources capacity era cpu regime control values shares op tier ξ dq old rr outcome view frame -∗
      (resources capacity era cpu regime control values shares op tier ξ dq old rr outcome view frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (tail op (KptMemory4.result (kind op) old) >>= continuation)) post) := by
  iintro #Hcert Hdata Hfinish
  iunfold memoryResources at Hdata
  icases Hdata with ⟨Hpacket,Hrun,Hword,Hresv,Hreceipts,Hview,Hframe⟩
  cases op with
  | loadFirst =>
    ihave ⟨Hregs,Hsaved,Htr⟩ := (packet_common capacity era cpu regime control values shares).mp $$ Hpacket
    isimp only [tail,kind,KptMemory4.result]
    iapply RegisterPlan.fold capacity.machine (footprint shares) (footprint_unique shares)
      image fixed whole gen era cpu (entry control cpu values) _ _ continuation post
      (load_tail_plan shares control cpu values old) $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ihave Hsaved : packetFrame capacity era cpu control (HartTp.set values 15#5 (old.signExtend 64)) shares $$ [Hsaved]
    · rw [packet_frame_load]; iexact Hsaved
    ihave Hpacket := (packet_common capacity era cpu regime control (HartTp.set values 15#5 (old.signExtend 64)) shares).mpr $$ [Hregs Hsaved Htr]
    · iframe
    iapply Hfinish
    iunfold resources
    isimp only [afterMap,kind]
    isimp only [kind] at Hword
    iframe
  | loadAgain =>
    ihave ⟨Hregs,Hsaved,Htr⟩ := (packet_common capacity era cpu regime control values shares).mp $$ Hpacket
    isimp only [tail,kind,KptMemory4.result]
    iapply RegisterPlan.fold capacity.machine (footprint shares) (footprint_unique shares)
      image fixed whole gen era cpu (entry control cpu values) _ _ continuation post
      (load_tail_plan shares control cpu values old) $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ihave Hsaved : packetFrame capacity era cpu control (HartTp.set values 15#5 (old.signExtend 64)) shares $$ [Hsaved]
    · rw [packet_frame_load]; iexact Hsaved
    ihave Hpacket := (packet_common capacity era cpu regime control (HartTp.set values 15#5 (old.signExtend 64)) shares).mpr $$ [Hregs Hsaved Htr]
    · iframe
    iapply Hfinish
    iunfold resources
    isimp only [afterMap,kind]
    isimp only [kind] at Hword
    iframe
  | storeNoff =>
    isimp only [tail,kind,KptMemory4.result,storeTail,BootPmp.sail_pure_bind]
    iapply Hfinish
    iunfold resources
    isimp only [afterMap,kind]
    isimp only [kind] at Hword
    iframe
  | storeIntena =>
    isimp only [tail,kind,KptMemory4.result,storeTail,BootPmp.sail_pure_bind]
    iapply Hfinish
    iunfold resources
    isimp only [afterMap,kind]
    isimp only [kind] at Hword
    iframe

theorem wp_body : ∀ regime shares control values, Config regime control →
    ∀ op tier ξ dq old rr, MycpuRegimeShell.Admits regime tier →
    (kind op = .store → dq = .own 1) →
    ∀ image fixed whole gen era cpu (frame : IProp GF) continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatumWord4.word capacity.translation era tier ξ (address cpu values op) dq old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu regime control values shares op tier ξ dq old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (body op >>= continuation)) post) := by
  intro regime shares control values config op tier ξ dq old rr admitted full image fixed whole gen era cpu frame continuation post
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hpacket Hrun Hword Hresv Hframe Hfinish
  ihave ⟨Hregs,Hsaved,Htr⟩ := (packet_common capacity era cpu regime control values shares).mp $$ Hpacket
  rw [factor]
  have complete : ∀ (op : Op),
      (kind op = .store → dq = .own 1) →
      iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
        RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) (entry control cpu values) (footprint shares) -∗
        packetFrame capacity era cpu control values shares -∗ MycpuRegimeShell.translation capacity era cpu regime -∗
        TsoContextReadWP.running capacity.machine era cpu ξ -∗
        KernelDatumWord4.word capacity.translation era tier ξ (address cpu values op) dq old -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
        finish capacity image fixed whole gen era cpu regime control values shares op tier ξ dq old rr frame continuation post -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu
          (KptMemory4.program (kind op) (address cpu values op) (sourceValue cpu values) >>= fun result => tail op result >>= continuation)) post) := by
    intro operation full
    iintro #Hcert Hregs Hsaved Htr Hrun Hword Hresv Hframe Hfinish
    ihave Hpacket := (packet_common capacity era cpu regime control values shares).mpr $$ [Hregs Hsaved Htr]
    · iframe
    iapply wp_memory capacity regime shares control values config operation tier ξ dq old rr admitted full
      image fixed whole gen era cpu frame (fun result => tail operation result >>= continuation) post
      $$ Hcert Hpacket Hrun Hword Hresv Hframe
    iunfold memoryFinish
    iapply guards_frame regime (entry control cpu values) operation (address cpu values operation)
      (P := fun outcome view => iprop(resources capacity era cpu regime control values shares operation tier ξ dq old rr outcome view frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post))
      (R := MachineInterp.generationCertificate capacity.machine fixed gen era) (next := ?_) $$ [Hfinish]
    · intro outcome view
      iintro ⟨#Hcert,Hfinish⟩ Hdata
      iapply wp_tail capacity regime shares control values operation tier ξ dq old rr outcome view
        image fixed whole gen era cpu frame continuation post $$ Hcert Hdata Hfinish
    · iframe Hcert
      isimp only [finish] at Hfinish
      iexact Hfinish
  cases op with
  | loadFirst =>
    isimp only [factored,BootPmp.sail_bind_assoc]
    iapply RegisterPlan.fold capacity.machine (footprint shares) (footprint_unique shares)
      image fixed whole gen era cpu (entry control cpu values) _ _ _ post
      (base_plan shares control cpu values) $$ Hcert Hregs
    iintro %base %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (KptMemory4.program (kind .loadFirst) (address cpu values .loadFirst) (sourceValue cpu values) >>= fun result => tail .loadFirst result >>= continuation)) post)
    iapply complete .loadFirst full $$ Hcert Hregs Hsaved Htr Hrun Hword Hresv Hframe Hfinish
  | loadAgain =>
    isimp only [factored,BootPmp.sail_bind_assoc]
    iapply RegisterPlan.fold capacity.machine (footprint shares) (footprint_unique shares)
      image fixed whole gen era cpu (entry control cpu values) _ _ _ post
      (base_plan shares control cpu values) $$ Hcert Hregs
    iintro %base %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (KptMemory4.program (kind .loadAgain) (address cpu values .loadAgain) (sourceValue cpu values) >>= fun result => tail .loadAgain result >>= continuation)) post)
    iapply complete .loadAgain full $$ Hcert Hregs Hsaved Htr Hrun Hword Hresv Hframe Hfinish
  | storeNoff =>
    isimp only [factored,BootPmp.sail_bind_assoc]
    iapply RegisterPlan.fold capacity.machine (footprint shares) (footprint_unique shares)
      image fixed whole gen era cpu (entry control cpu values) _ _ _ post
      (source_plan shares control cpu values) $$ Hcert Hregs
    iintro %source %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply RegisterPlan.fold capacity.machine (footprint shares) (footprint_unique shares)
      image fixed whole gen era cpu (entry control cpu values) _ _ _ post
      (base_plan shares control cpu values) $$ Hcert Hregs
    iintro %base %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (KptMemory4.program (kind .storeNoff) (address cpu values .storeNoff) (sourceValue cpu values) >>= fun result => tail .storeNoff result >>= continuation)) post)
    iapply complete .storeNoff full $$ Hcert Hregs Hsaved Htr Hrun Hword Hresv Hframe Hfinish
  | storeIntena =>
    isimp only [factored,BootPmp.sail_bind_assoc]
    iapply RegisterPlan.fold capacity.machine (footprint shares) (footprint_unique shares)
      image fixed whole gen era cpu (entry control cpu values) _ _ _ post
      (source_plan shares control cpu values) $$ Hcert Hregs
    iintro %source %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply RegisterPlan.fold capacity.machine (footprint shares) (footprint_unique shares)
      image fixed whole gen era cpu (entry control cpu values) _ _ _ post
      (base_plan shares control cpu values) $$ Hcert Hregs
    iintro %base %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (KptMemory4.program (kind .storeIntena) (address cpu values .storeIntena) (sourceValue cpu values) >>= fun result => tail .storeIntena result >>= continuation)) post)
    iapply complete .storeIntena full $$ Hcert Hregs Hsaved Htr Hrun Hword Hresv Hframe Hfinish
end Xv6.Kernel.PushOffWord4
