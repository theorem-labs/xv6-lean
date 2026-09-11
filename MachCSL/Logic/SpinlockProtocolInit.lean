import MachCSL.Logic.SpinlockProtocolWords
import MachCSL.Logic.LockProofs

namespace MachCSL.Logic.SpinlockProtocol
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance wordAt_timeless era a v t : Timeless (wordAt capacity era a v t) := by
  unfold wordAt TsoStore.storedWindow TsoStore.storedByte
  unfold Tso.physBytePointsto Tso.timestampElem
  infer_instance

instance body_timeless era γ : Timeless (body capacity era γ) := by
  unfold body
  infer_instance

instance won_timeless era γ cpu B : Timeless (won capacity era γ cpu B) := by
  unfold won Tso.Views.viewLB Tso.History.logElem
  infer_instance

theorem holder_exclusive (era : Era.Record) (γ : GName) (cpu other : CPU) (B C : Nat) :
    iprop(⊢ won capacity era γ cpu B -∗ won capacity era γ other C -∗ False) := by
  unfold won
  iintro ⟨Hfirst, _⟩ ⟨Hsecond, _⟩
  iapply Lock.fragAt_exclusive capacity.lock γ (some (cpu, false)) (some (other, false)) B C $$ Hfirst Hsecond

variable [Platform] {hlc : HasLC} [InvGS_gen hlc GF]

instance isLock_persistent N era γ : Persistent (isLock capacity N era γ) := by
  unfold isLock
  infer_instance

instance idle_persistent fixed gen era N γ cpu :
    Persistent (resource capacity fixed gen era N γ cpu .idle) := by
  unfold resource payload MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
  infer_instance

omit [Platform] in
theorem allocate (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record) (N : Namespace) :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      wordAt capacity era SpinlockImage.lockAddress 0#32 0 -∗
      wordAt capacity era SpinlockImage.counterAddress 0#32 0 ={⊤}=∗
      ∃ γ, isLock capacity N era γ ∗ ∀ cpu, resource capacity fixed gen era N γ cpu .idle) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hlock Hcounter
  imod Lock.allocate_free capacity.lock with ⟨%γ, Ha, Hf⟩
  imod inv_alloc N ⊤ (body capacity era γ) $$ [Hlock Hcounter Ha Hf] with #Hinv
  · iintro !>
    unfold body
    iexists 0
    iexists 0
    ileft
    iframe Hlock Ha Hf
    iexists 0#32
    iexists 0
    iexact Hcounter
  · imodintro
    iexists γ
    isplit
    · unfold isLock
      iexact Hinv
    · iintro %cpu
      unfold resource payload isLock
      iframe Hcert Hinv

end MachCSL.Logic.SpinlockProtocol
