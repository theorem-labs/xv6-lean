import MachCSL.Logic.TsoHistoryProofs
import MachCSL.Logic.TsoViewsProofs
import MachCSL.Logic.TsoOwnership

/-! Explicit linking of the three proved interfaces in the six-slot partial registry. -/
namespace MachCSL.Logic.Tso.History

theorem registryHistorySpec : HistorySpec registryCapacity := historySpec registryCapacity
theorem registryViewsSpec : Views.ViewsSpec viewsCapacity := Views.viewsSpec viewsCapacity
theorem registryLedgerSpec : Tso.LedgerSpec ledgerCapacity := Tso.ledgerSpec ledgerCapacity

end MachCSL.Logic.Tso.History
