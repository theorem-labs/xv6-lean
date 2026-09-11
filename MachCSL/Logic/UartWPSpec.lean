import MachCSL.Logic.UartWPDefs

namespace MachCSL.Logic.UartWP
open Iris Iris.BI MachCSL.Machine

/-- Independent contract: explicit invariant namespaces, names and ledger hooks.
No source implementation module is imported here. -/
structure UartWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (ghost : UartGhost.Capacity GF) : Prop where
  uartAllocate : ∀ N E era names u,
    iprop(⊢ Device.uartFrag capacity.era.devices era.uart u -∗ UartGhost.ghosts ghost names u
      ={E}=∗ uartInv capacity ghost N era names)
  initialAllocate : ∀ N E era u,
    iprop(⊢ Device.uartFrag capacity.era.devices era.uart u ={E}=∗ ∃ names,
      uartInv capacity ghost N era names ∗ UartGhost.initialClients ghost names u)
  plicAllocate : ∀ N E era p, Devices.Plic.PlicPlanOK p →
    iprop(⊢ Device.plicFrag capacity.era.devices era.plic p ={E}=∗ plicInv capacity N era)
  trivialPermit : ∀ (Nuart Nobs : Namespace) γ names, (↑Nobs : CoPset) ⊆ ⊤ \ ↑Nuart →
    iprop(⊢ ObservationInvariant.trivial capacity.power Nobs γ -∗ obsPermit capacity ghost Nuart γ names)
  ledgerPermit : ∀ (Nuart Nobs : Namespace) γ names R, (∀ history, Timeless (R history)) →
    (↑Nobs : CoPset) ⊆ ⊤ \ ↑Nuart →
    iprop(⊢ txLedgerLaw ghost Nuart Nobs names R) →
    iprop(⊢ rxLedgerLaw ghost Nuart Nobs names R) →
    iprop(⊢ ObservationInvariant.ledger capacity.power Nobs γ R -∗ obsPermit capacity ghost Nuart γ names)
  loop : ∀ image fixed whole generation era Nuart Nplic names post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      uartInv capacity ghost Nuart era names -∗ plicInv capacity Nplic era -∗
      obsPermit capacity ghost Nuart fixed.observations names -∗
      DeadThread.threadWP capacity image fixed whole (.uart generation) post)
  trivialLoop : ∀ image fixed whole generation era (Nuart Nplic Nobs : Namespace) names post,
    (↑Nobs : CoPset) ⊆ ⊤ \ ↑Nuart →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      uartInv capacity ghost Nuart era names -∗ plicInv capacity Nplic era -∗
      ObservationInvariant.trivial capacity.power Nobs fixed.observations -∗
      DeadThread.threadWP capacity image fixed whole (.uart generation) post)
  ledgerLoop : ∀ image fixed whole generation era (Nuart Nplic Nobs : Namespace) names post R,
    (∀ history, Timeless (R history)) → (↑Nobs : CoPset) ⊆ ⊤ \ ↑Nuart →
    iprop(⊢ txLedgerLaw ghost Nuart Nobs names R) →
    iprop(⊢ rxLedgerLaw ghost Nuart Nobs names R) →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed generation era -∗
      uartInv capacity ghost Nuart era names -∗ plicInv capacity Nplic era -∗
      ObservationInvariant.ledger capacity.power Nobs fixed.observations R -∗
      DeadThread.threadWP capacity image fixed whole (.uart generation) post)

end MachCSL.Logic.UartWP
