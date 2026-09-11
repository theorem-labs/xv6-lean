import MachCSL.Logic.SpinlockProtocolDefs

namespace MachCSL.Logic.SpinlockProtocol
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- Native allocation, resource callbacks and holder-fragment exclusion; inhabited by `actual`. -/
structure SpinlockProtocolSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  allocate : ∀ fixed gen era N,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      wordAt capacity era SpinlockImage.lockAddress 0#32 0 -∗
      wordAt capacity era SpinlockImage.counterAddress 0#32 0 ={⊤}=∗
      ∃ γ, isLock capacity N era γ ∗ ∀ cpu, resource capacity fixed gen era N γ cpu .idle)
  access : ∀ fixed gen era N γ cpu,
    EventPlan.Access capacity.machine fixed gen era cpu relations
      (resource capacity fixed gen era N γ cpu)
  holderExclusive : ∀ era γ cpu other B C,
    iprop(⊢ won capacity era γ cpu B -∗ won capacity era γ other C -∗ False)

end MachCSL.Logic.SpinlockProtocol
