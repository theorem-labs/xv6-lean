import Xv6.Kernel.Sv39AddressSpec
import MachCSL.Logic.RegisterPlanProofs

namespace Xv6.Kernel.Sv39Address
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

private theorem fold {fp : RegisterFootprint.Footprint} (unique : RegisterFootprint.Unique fp)
    {rs : RegisterFile} {body : SailM α} {program : SailM β} {tail : α → SailM β}
    (cut : Boundary fp rs body program tail)
    image fixed whole gen era cpu (continuation : β → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      (RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (body >>= fun result => tail result >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | body =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hfinish
    iapply Hfinish $$ Hregs
  | «prefix» before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hfinish
    iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs _
      (fun value after => value = _ ∧ after = rs) _ post before $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply ih $$ Hcert Hregs Hfinish

variable (pureSpec : PureSpec)
include pureSpec

theorem wp_canonical shares rs tree (config : Config rs (PtTree.base tree)) address access
    (supported : Supported access) (effective : Effective rs access) (canon : Canonical address)
    image fixed whole gen era cpu (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu rs shares -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (KptTranslate.program 0#16 tree (vpn address) access (mxr rs) (doSum rs) >>=
            fun response => resume address access response >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address access >>= continuation)) post) :=
  fold capacity (pureSpec.unique shares)
    (pureSpec.canonical shares rs tree config address access supported effective canon)
    image fixed whole gen era cpu continuation post

theorem wp_noncanonical shares rs root (config : Config rs root) address access
    (supported : Supported access) (effective : Effective rs access) (canon : ¬ Canonical address)
    image fixed whole gen era cpu (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu rs shares -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Err (pageFault access, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address access >>= continuation)) post) := by
  iintro #Hcert Hregs Hfinish
  iapply RegisterPlan.fold capacity (footprint shares) (pureSpec.unique shares)
    image fixed whole gen era cpu rs _ (fun value after => value = .Err (pageFault access, ()) ∧ after = rs)
    continuation post (pureSpec.noncanonical shares rs root config address access supported effective canon)
    $$ Hcert Hregs
  iintro %value %after %same Hregs
  rcases same with ⟨rfl,rfl⟩
  iapply Hfinish $$ Hregs

theorem wp_suffix address access (supported : Supported access) response
    image fixed whole gen era cpu (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (continuation (resumed address access response))) post -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (resume address access response >>= continuation)) post) := by
  iintro #Hcert Hfinish
  iapply RegisterPlan.fold capacity [] (by simp [RegisterFootprint.Unique])
    image fixed whole gen era cpu zeroRegisters _
    (fun value after => value = resumed address access response ∧ after = zeroRegisters)
    continuation post (pureSpec.suffix zeroRegisters address access supported response) $$ Hcert []
  · iunfold RegisterFootprint.cells
    itrivial
  iintro %value %after %same _
  rcases same with ⟨rfl,rfl⟩
  iexact Hfinish

theorem actual : Spec capacity := ⟨wp_canonical capacity pureSpec, wp_noncanonical capacity pureSpec,
  wp_suffix capacity pureSpec⟩

end Xv6.Kernel.Sv39Address
