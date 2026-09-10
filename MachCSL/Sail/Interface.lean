import Sail.ConcurrencyInterfaceV1Free

/-! The pinned free-event interface is a dependency of the eventual system model.
These checks establish that effects remain observable. They do not instantiate
RISC-V registers, memory constraints, exclusive atomicity or the CPU loop. -/
namespace MachCSL.Sail

open _root_.Sail.ConcurrencyInterfaceV1.Free

variable {Register : Type} (RegisterType : Register → Type) [_root_.Sail.ConcurrencyInterfaceV1.Arch]

/-- An emitted hardware event cannot be extracted as a pure constant. -/
theorem emitted_event_not_pure (event : Event RegisterType ue) :
    ¬ IsPure (emit event) := by
  exact fun h => h

end MachCSL.Sail
