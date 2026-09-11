import MachCSL.Logic.RegisterProofs
import MachCSL.Logic.TsoHistoryLink

/-! Explicit contract linking at the seven-slot registry; device slots remain free. -/
namespace MachCSL.Logic.Registers

theorem registryRegisterSpec : RegisterSpec registryCapacity := registerSpec registryCapacity
theorem registryHistorySpec : Tso.History.HistorySpec historyCapacity :=
  Tso.History.historySpec historyCapacity
theorem registryViewsSpec : Tso.Views.ViewsSpec viewsCapacity := Tso.Views.viewsSpec viewsCapacity
theorem registryLedgerSpec : Tso.LedgerSpec ledgerCapacity := Tso.ledgerSpec ledgerCapacity

end MachCSL.Logic.Registers
