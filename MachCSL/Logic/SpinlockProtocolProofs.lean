import MachCSL.Logic.SpinlockProtocolCommit

namespace MachCSL.Logic.SpinlockProtocol
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem write_access (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (N : Namespace) (γ : GName) (cpu : CPU) :
    EventPlan.WriteAccess capacity.machine era cpu relations
      (resource capacity fixed gen era N γ cpu) := by
  intro phase rr n req value mode enabled eligible
  unfold resource
  iintro ⟨#Hcert, #Hinv, Hpayload⟩ %g %fact Hbundle Htso
  iunfold isLock at Hinv
  iunfold inv at Hinv
  imod Hinv $$ %(⊤ : CoPset) [] with ⟨Hbody, Hclose⟩
  · ipureintro; exact fun _ _ => CoPset.mem_full
  · imod Hbody
    iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact False.elim (CoPset.mem_empty h))
    iintro Hback
    iintro !>
    imod commit (hlc := hlc) capacity era γ cpu g phase rr n req value mode eligible $$
      Hbody Hpayload [] Hbundle Htso with ⟨Hbody, Hbundle, Htso, Hnext⟩
    · ipureintro; exact fact
    · imod Hback
      imod Hclose $$ [Hbody] with _
      · iintro !>; iexact Hbody
      · imodintro
        iframe Hbundle Htso
        iintro Hview
        ihave ⟨%next, %step, Hpayload⟩ := Hnext $$ Hview
        iexists next
        isplit
        · ipureintro; exact step
        · unfold isLock inv
          iframe Hcert Hinv Hpayload

omit [Platform] in
theorem barrier_access (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (N : Namespace) (γ : GName) (cpu : CPU) :
    EventPlan.BarrierAccess capacity.machine era relations
      (resource capacity fixed gen era N γ cpu) := by
  intro phase kind enabled
  obtain ⟨next, step⟩ := enabled
  cases step with
  | fence B v t =>
    unfold BarrierWP.ghostStep
    iintro %g Hheap Htso HR
    imodintro
    iframe Hheap Htso
    iexists (Phase.stored B v t)
    iframe HR
    ipureintro
    exact BarrierStep.fence B v t

theorem access (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (N : Namespace) (γ : GName) (cpu : CPU) :
    EventPlan.Access capacity.machine fixed gen era cpu relations
      (resource capacity fixed gen era N γ cpu) where
  plain := plain_access capacity fixed gen era N γ cpu
  exclusive := exclusive_access capacity fixed gen era N γ cpu
  write := write_access capacity fixed gen era N γ cpu
  barrier := barrier_access capacity fixed gen era N γ cpu

theorem actual : SpinlockProtocolSpec capacity where
  allocate := allocate capacity
  access := access capacity
  holderExclusive := holder_exclusive capacity

end MachCSL.Logic.SpinlockProtocol
